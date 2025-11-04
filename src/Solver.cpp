#include "Solver.h"
#include <iostream>

namespace yaga {

Solver::Solver(const terms::Term_manager& tm) : solver_trail(dispatcher), term_manager(tm)
{
    subsumption = std::make_unique<Subsumption>();
    dispatcher.add(subsumption.get());
}

Solver::Solver() : Solver(terms::Term_manager()) {}

std::vector<Clause> Solver::propagate() { return theory()->propagate(database, solver_trail); }

std::pair<std::vector<Clause>, int> Solver::analyze_conflicts(std::vector<Clause>&& conflicts)
{
    ++total_conflicts;
    std::vector<Clause> learned;
    int level = std::numeric_limits<int>::max();
    for (auto&& conflict : conflicts)
    {
        ++total_conflict_clauses;

        // derive clause suitable for backtracking
        auto [clause, clause_level] =
            analysis.analyze(trail(), std::move(conflict), [&](auto const& other_clause) {
                dispatcher.on_conflict_resolved(db(), trail(), other_clause);
            });

        if (!clause.empty())
        {
            subsumption->minimize(trail(), clause);
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

std::vector<Clause> Solver::analyze_final(std::vector<Clause>&& learned_clauses){

    std::vector<Clause> final;

    for (auto&& clause : learned_clauses){
        final.emplace_back(analysis.analyze_final(trail(), std::move(clause)));
    }
    return final;
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
            return lhs < rhs;
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
        ++total_learned_clauses;
        // add the clause to database
        auto& learned_ref = db().learn_clause(std::move(clause));
        // trigger events
        dispatcher.on_learned_clause(db(), trail(), learned_ref);
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
    dispatcher.on_before_backtrack(db(), trail(), level);

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
    theory()->decide(db(), trail(), var);
}

void Solver::decide(Variable var, TrailModelsSnapshot const& input_model){
    ++total_decisions;
    theory()->decide(db(), trail(), var, input_model);
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
        dispatcher.on_variable_resize(type, model->num_vars());
    }

    // reset solver state
    total_conflicts = 0;
    total_decisions = 0;
    total_restarts = 0;
    dispatcher.on_init(db(), trail());
}

void Solver::restart()
{
    dispatcher.on_before_backtrack(db(), trail(), /*decision_level=*/0);

    ++total_restarts;
    trail().clear();

    dispatcher.on_restart(db(), trail());
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
                std::cout << ">>> end check" << std::endl;
                return Result::unsat;
            }

            auto [learned, level] = analyze_conflicts(std::move(conflicts));
            if (std::any_of(learned.begin(), learned.end(), [](auto const& clause) { return clause.empty(); }))
            {
                std::cout << ">>> end check" << std::endl;
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
                std::cout << ">>> end check" << std::endl;
                return Result::sat;
            }
            decide(var.value());
        }
    }
}

void debug_print(std::vector<Clause> const& clauses, std::string debug_info){
    std::cout << debug_info << " " << clauses.size();
    for (auto&& c : clauses){
        std::cout << "\t";
        for(auto&& lit : c){
            std::cout << " " << lit.var() << " is_negation: " << static_cast<bool>(lit.is_negation());
        }
        std::cout << std::endl;
    }
}

Solver::Result Solver::check(TrailModelsSnapshot& input_model) {
    std::cout << std::boolalpha;
    init();

    for (;;)
    {
        std::cout << "<<<<< propagation" << std::endl;
        auto conflicts = propagate();

        if (!conflicts.empty())
        {
            debug_print(conflicts, "Found conflicts");
            //interpolant.insert(interpolant.end(), conflicts.begin(), conflicts.end());
            if (trail().decision_level() == 0)
            {
                return Result::unsat;
            }
            std::cout << "Analysis" << std::endl;
            auto [learned, level] = analyze_conflicts(std::move(conflicts));

            debug_print(learned, "learned clauses");
            //interpolant.insert(interpolant.end(), learned.begin(), learned.end());

            if (std::any_of(learned.begin(), learned.end(), [](auto const& clause) { return clause.empty(); })
                || level < input_model.size())
            {
                auto final = analyze_final(std::move(learned));
                debug_print(final, "Final_resolve " + std::to_string(level) + " num of clauses of interpolant");

                interpolant.insert(interpolant.end(), final.begin(), final.end());
                /*std::cout << "Printing and adding the literals to the interpolant one by one to precisely know which lit is representing which var";
                for (auto&& c : final){
                    std::cout << "\t";
                    for (auto&& lit : c){
                        std::cout << " " << lit.var() << " " << static_cast<bool>(lit.is_negation());
                        interpolant.emplace_back(std::vector{lit});
                    }
                    std::cout << std::endl;
                }*/
                std::cout << ">>> end of check modulo model" << std::endl;
                return Result::unsat;
            }

            std::cout << "learned" << std::endl;
            auto clauses = learn(std::move(learned));
            if (restart_policy->should_restart())
            {
                std::cout << "restart" << std::endl;
                input_model.restart();
                restart();
            }
            else // backtrack instead of restarting
            {
                std::cout << "backtrack to level " << level <<  std::endl;
                backtrack_with(clauses, level);
            }
        }
        else // no conflict
        {
            std::cout << "no conflict" << std::endl;
            //decide value from the input model
            if (trail().decision_level() < input_model.size())
            {
                std::cout << "decision from model, akt dec level " << trail().decision_level() << " input_model.size() " << input_model.size() << std::endl;
                for (size_t i = 0; i <= Variable::Type::LAST_ELEMENT; ++i)
                {
                    auto res = input_model.next_decision(static_cast<Variable::Type>(i));
                    if (res.has_value())
                    {
                        Variable var(res.value(), static_cast<Variable::Type>(i));
                        decide(var, input_model);

                        break;
                    }
                }
            }
            else { //if no previous decision then this branch
                std::cout << "decision heuristics ";
                auto var = pick_variable();
                std::cout << "Picked Variable " << var.value() << std::endl;
                if (!var)
                {
                    return Result::sat;
                }
                decide(var.value());
            }
        }
    }

}

} // namespace yaga