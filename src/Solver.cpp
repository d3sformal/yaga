#include "Solver.h"

namespace perun {

std::optional<Clause> Solver::propagate() { return theory->propagate(database, solver_trail); }

std::pair<Clause, int> Solver::analyze_conflict(Clause&& conflict)
{
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

void Solver::backtrack_with(Clause&& clause, int level)
{
    // add the clause to database
    auto& learned = db().learn_clause(std::move(clause));

    // trigger events
    for (auto listener : listeners())
    {
        listener->on_learned_clause(db(), trail(), &learned);
    }

    trail().backtrack(level);

    if (learned.size() >= 2 &&
        trail().decision_level(learned[0].var()) == trail().decision_level(learned[1].var()))
    {
        // decide the first or the second literal in `learned`
        trail().decide(learned[0].var());
        trail()
            .model<bool>(Variable::boolean)
            .set_value(learned[0].var().ord(), !learned[0].is_negation());
    }
    else // UIP
    {
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
    for (auto [type, model] : solver_trail.models())
    {
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
            auto [learned, level] = analyze_conflict(std::move(conflict.value()));
            if (learned.empty())
            {
                return unsat;
            }

            if (restart_policy->should_restart())
            {
                restart();
            }
            else // backtrack instead of restarting
            {
                backtrack_with(std::move(learned), level);
            }
        }
        else // no conflict
        {
            auto var = pick_variable();
            if (!var)
            {
                return sat;
            }
            decide(var.value());
        }
    }
}

} // namespace perun