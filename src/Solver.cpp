#include "Solver.h"

namespace perun {

std::optional<Clause> Solver::propagate()
{
    for (auto& theory : theories_)
    {
        auto conflict = theory->propagate(db_, trail_);
        if (conflict)
        {
            return conflict;
        }
    }
    return {};
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
    for (auto& theory : theories_)
    {
        theory->on_learned_clause(db_, trail_, &learned);
    }
    restart_->on_learned_clause(db_, trail_, &learned);
    variable_order_->on_learned_clause(db_, trail_, &learned);

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
    for (auto& theory : theories_)
    {
        theory->decide(db_, trail_, var);
    }
}

void Solver::init()
{
    num_conflicts_ = 0;
    num_decisions_ = 0;
    num_restarts_ = 0;

    for (auto [type, model] : trail_.models())
    {
        variable_order_->on_variable_resize(type, model->num_vars());
        subsumption_.on_variable_resize(type, model->num_vars());
    }
    variable_order_->on_init(db_, trail_);
}

void Solver::restart()
{
    ++num_restarts_;
    trail_.clear();
    restart_->on_restart(db_, trail_);
    subsumption_.on_restart(db_, trail_);
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
            subsumption_.on_conflict_clause(db_, trail_, learned);

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