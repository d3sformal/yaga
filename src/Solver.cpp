#include "Solver.h"

namespace perun {

std::optional<Clause> Solver::propagate() { return theory->propagate(database, solver_trail); }

std::pair<Clause, int> Solver::analyze_conflict(Clause&& conflict)
{
    // notify listeners that number of variables has changed if conflict introduces new variables
    int new_num_vars = static_cast<int>(trail().model<bool>(Variable::boolean).num_vars());
    if (num_bool_vars != new_num_vars)
    {
        num_bool_vars = new_num_vars;
        for (auto listener : listeners())
        {
            listener->on_variable_resize(Variable::boolean, num_bool_vars);
        }
    }

    // derive clause suitable for backtracking
    auto [learned, level] =
        analysis.analyze(trail(), std::move(conflict), [&](auto const& other_clause) {
            for (auto listener : listeners())
            {
                listener->on_conflict_resolved(db(), trail(), other_clause);
            }
        });

    if (!learned.empty())
    {
        ++total_conflicts;
        subsumption.minimize(trail(), learned);
    }
    return {learned, level};
}

Clause& Solver::learn(Clause&& clause)
{
    // add the clause to database
    auto& learned = db().learn_clause(std::move(clause));
    // trigger events
    for (auto listener : listeners())
    {
        listener->on_learned_clause(db(), trail(), learned);
    }
    return learned;
}

bool Solver::is_semantic_split(Clause const& clause) const
{
    return clause.size() >= 2 && trail().decision_level(clause[0].var()).value() ==
                                     trail().decision_level(clause[1].var()).value();
}

void Solver::backtrack_with(Clause& learned, int level)
{
    for (auto listener : listeners())
    {
        listener->on_before_backtrack(db(), trail(), level);
    }

    if (is_semantic_split(learned))
    {
        // find the best variable to decide
        auto top_it = learned.begin();
        auto top_level = trail().decision_level(top_it->var()).value();
        for (auto it = top_it + 1; it != learned.end() && trail().decision_level(it->var()) == top_level; ++it)
        {
            assert(trail().reason(it->var()) == nullptr);
            if (variable_order->is_before(it->var(), top_it->var()))
            {
                top_it = it;
            }
        }

        trail().backtrack(level);
        // decide one of the literals at the highest decision level
        trail().decide(top_it->var());
        trail()
            .model<bool>(Variable::boolean)
            .set_value(top_it->var().ord(), !top_it->is_negation());
    }
    else // UIP
    {
        trail().backtrack(level);
        // propagate the top level literal at assertion level
        trail().propagate(learned[0].var(), &learned, level);
        trail()
            .model<bool>(Variable::boolean)
            .set_value(learned[0].var().ord(), !learned[0].is_negation());
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
        auto conflict = propagate();
        if (conflict)
        {
            if (trail().decision_level() == 0)
            {
                return Result::unsat;
            }

            auto [learned, level] = analyze_conflict(std::move(conflict.value()));
            if (learned.empty())
            {
                return Result::unsat;
            }

            auto& learned_ref = learn(std::move(learned));
            if (restart_policy->should_restart())
            {
                restart();
            }
            else // backtrack instead of restarting
            {
                backtrack_with(learned_ref, level);
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