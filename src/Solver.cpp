#include "Solver.h"

namespace perun {

std::optional<Clause> Solver::propagate()
{
    return theory_->propagate(db_, trail_);
}

std::pair<Clause, int> Solver::analyze_conflict(Clause&& conflict)
{
    auto[learned, level] = analysis_.analyze(trail_, std::move(conflict), [&](const auto& other_clause) {
        variable_order_->on_conflict_resolved(db_, trail_, other_clause);
    });
    return {learned, level};
}

void Solver::backtrack_with(Clause&& clause, int level)
{
    // add the clause to database
    auto& learned = db_.learn_clause(std::move(clause));

    // trigger events
    for (auto listener : listeners())
    {
        listener->on_learned_clause(db_, trail_, &learned);
    }

    // TODO: handle semantic split (decide clause[0] or clause[1] instead of propagating clause[0])

    // propagate the top level literal at assertion level
    trail_.backtrack(level);
    trail_.propagate(learned[0].var(), &learned, level);
    trail_.model<bool>(Variable::boolean).set_value(learned[0].var().ord(), !learned[0].is_negation());
}

std::optional<Variable> Solver::pick_variable()
{
    return variable_order_->pick(db_, trail_);
}

void Solver::decide(Variable var)
{
    ++num_decisions_;
    theory_->decide(db_, trail_, var);
}

void Solver::init()
{
    // allocate memory
    for (auto [type, model] : trail_.models())
    {
        for (auto listener : listeners())
        {
            listener->on_variable_resize(type, model->num_vars());
        }
    }

    // reset solver state
    num_conflicts_ = 0;
    num_decisions_ = 0;
    num_restarts_ = 0;
    for (auto listener : listeners())
    {
        listener->on_init(db_, trail_);
    }
}

void Solver::restart()
{
    ++num_restarts_;
    trail_.clear();

    for (auto listener : listeners())
    {
        listener->on_restart(db_, trail_);
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
            auto[learned, level] = analyze_conflict(std::move(conflict.value()));
            if (learned.empty())
            {
                return unsat;
            }

            ++num_conflicts_;
            for (auto listener : listeners())
            {
                listener->on_conflict_derived(db_, trail_, learned);
            }

            if (restart_->should_restart())
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

}