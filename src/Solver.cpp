#include "Solver.h"

namespace perun {

std::vector<Clause> Solver::propagate() { return theory->propagate(database, solver_trail); }

std::pair<std::vector<Clause>, int> Solver::analyze_conflicts(std::vector<Clause>&& conflicts)
{
    // notify listeners that number of variables has changed if a conflict introduces new variables
    int new_num_vars = static_cast<int>(trail().model<bool>(Variable::boolean).num_vars());
    if (num_bool_vars != new_num_vars)
    {
        num_bool_vars = new_num_vars;
        for (auto listener : listeners())
        {
            listener->on_variable_resize(Variable::boolean, num_bool_vars);
        }
    }

    std::vector<Clause> learned;
    int level = std::numeric_limits<int>::max();
    for (auto&& conflict : conflicts)
    {
        ++total_conflicts;

        // derive clause suitable for backtracking
        auto [clause, clause_level] =
            analysis.analyze(trail(), std::move(conflict), [&](auto const& other_clause) {
                for (auto listener : listeners())
                {
                    listener->on_conflict_resolved(db(), trail(), other_clause);
                }
            });

        if (!clause.empty())
        {
            subsumption.minimize(trail(), clause);
        }

        // find all conflict clauses at the lowest decision level
        if (clause_level < level)
        {
            level = clause_level;
            learned.clear();
            learned.push_back(std::move(clause));
        }
        else if (clause_level == level)
        {
            learned.push_back(std::move(clause));
        }
    }
    return {learned, level};
}

Solver::Clause_range Solver::learn(std::vector<Clause>&& clauses)
{
    // remove duplicate clauses
    std::sort(clauses.begin(), clauses.end(), [](auto const& lhs, auto const& rhs) {
        if (lhs.size() < rhs.size())
        {
            return true;
        }
        else if (lhs.size() > rhs.size())
        {
            return false;
        }
        else // lhs.size() == rhs.size()
        {
            auto [lhs_it, rhs_it] = std::mismatch(lhs.begin(), lhs.end(), rhs.begin());
            return lhs_it->var().ord() < rhs_it->var().ord();
        }
    });
    clauses.erase(std::unique(clauses.begin(), clauses.end()), clauses.end());

    // prefer UIP clauses (propagations) over semantic split clauses (decisions)
    if (std::any_of(clauses.begin(), clauses.end(), [&](auto const& learned) {
        return !is_semantic_split(learned);
    }))
    {
        clauses.erase(std::remove_if(clauses.begin(), clauses.end(), [&](auto const& learned) {
            return is_semantic_split(learned);
        }), clauses.end());
    }

    for (auto const& clause : clauses)
    {
        // add the clause to database
        auto& learned_ref = db().learn_clause(std::move(clause));
        // trigger events
        for (auto listener : listeners())
        {
            listener->on_learned_clause(db(), trail(), learned_ref);
        }
    }
    return {db().learned().begin() + (db().learned().size() - clauses.size()), 
            db().learned().end()};
}

bool Solver::is_semantic_split(Clause const& clause) const
{
    return clause.size() >= 2 && trail().decision_level(clause[0].var()).value() ==
                                     trail().decision_level(clause[1].var()).value();
}

void Solver::backtrack_with(Clause_range clauses, int level)
{
    for (auto listener : listeners())
    {
        listener->on_before_backtrack(db(), trail(), level);
    }

    auto& model = trail().model<bool>(Variable::boolean);
    if (is_semantic_split(clauses[0]))
    {
        assert(std::all_of(clauses.begin(), clauses.end(), [&](auto const& other_clause) {
            return is_semantic_split(other_clause);
        }));

        // find the best variable to decide
        auto top_it = clauses[0].begin();
        auto top_level = trail().decision_level(top_it->var()).value();
        auto it = top_it + 1;
        for (; it != clauses[0].end() && trail().decision_level(it->var()) == top_level; ++it)
        {
            assert(trail().reason(it->var()) == nullptr);
            if (variable_order->is_before(it->var(), top_it->var()))
            {
                top_it = it;
            }
        }

        // We have to backtrack a semantic decision. Otherwise, the proof of MCSat termination 
        // does not hold and the solver is not guaranteed to terminate.
        assert(trail().decision_level() >= level + 1);
        assert(trail().assigned(level + 1).front().var.type() != Variable::boolean);

        trail().backtrack(level);
        // decide one of the literals at the highest decision level
        trail().decide(top_it->var());
        model.set_value(top_it->var().ord(), !top_it->is_negation());
    }
    else // UIP
    {
        assert(std::all_of(clauses.begin(), clauses.end(), [&](auto const& other_clause) {
            return !is_semantic_split(other_clause);
        }));

        trail().backtrack(level);

        // propagate top level literals from all clauses
        for (auto& clause : clauses)
        {
            if (!model.is_defined(clause[0].var().ord()))
            {
                trail().propagate(clause[0].var(), &clause, level);
                model.set_value(clause[0].var().ord(), !clause[0].is_negation());
            }
        }
    }
}

std::optional<Variable> Solver::pick_variable() { return variable_order->pick(db(), trail()); }

void Solver::decide(Variable var)
{
    ++total_decisions;
    theory->decide(db(), trail(), var);
}

void Solver::init()
{
    // allocate memory
    for (auto [type, model] : trail().models())
    {
        if (type == Variable::boolean)
        {
            num_bool_vars = model->num_vars();
        }
        for (auto listener : listeners())
        {
            listener->on_variable_resize(type, model->num_vars());
        }
    }

    // reset solver state
    total_conflicts = 0;
    total_decisions = 0;
    total_restarts = 0;
    for (auto listener : listeners())
    {
        listener->on_init(db(), trail());
    }
}

void Solver::restart()
{
    for (auto listener : listeners())
    {
        listener->on_before_backtrack(db(), trail(), /*decision_level=*/0);
    }

    ++total_restarts;
    trail().clear();

    for (auto listener : listeners())
    {
        listener->on_restart(db(), trail());
    }
}

Solver::Result Solver::check()
{
    init();

    for (;;)
    {
        auto conflicts = propagate();
        if (!conflicts.empty())
        {
            if (trail().decision_level() == 0)
            {
                return Result::unsat;
            }

            auto [learned, level] = analyze_conflicts(std::move(conflicts));
            if (std::any_of(learned.begin(), learned.end(), [](auto const& clause) { return clause.empty(); }))
            {
                return Result::unsat;
            }

            auto clauses = learn(std::move(learned));
            if (restart_policy->should_restart())
            {
                restart();
            }
            else // backtrack instead of restarting
            {
                backtrack_with(clauses, level);
            }
        }
        else // no conflict
        {
            auto var = pick_variable();
            if (!var)
            {
                return Result::sat;
            }
            decide(var.value());
        }
    }
}

} // namespace perun