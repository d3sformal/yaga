#include "Theory_combination.h"

namespace perun {

std::optional<Clause> Theory_combination::propagate(Database& db, Trail& trail)
{
    for (;;)
    {
        auto old_size = trail.assigned(trail.decision_level()).size();
        for (auto& theory : theories)
        {
            if (auto conflict = theory->propagate(db, trail))
            {
                return conflict;
            }
        }

        // if no new propagations were made
        if (old_size == trail.assigned(trail.decision_level()).size())
        {
            break;
        }
    }
    return {};
}

void Theory_combination::decide(Database& db, Trail& trail, Variable var)
{
    for (auto& theory : theories)
    {
        theory->decide(db, trail, var);
    }
}

void Theory_combination::on_init(Database& db, Trail& trail)
{
    for (auto& theory : theories)
    {
        theory->on_init(db, trail);
    }
}

void Theory_combination::on_variable_resize(Variable::Type type, int num_vars)
{
    for (auto& theory : theories)
    {
        theory->on_variable_resize(type, num_vars);
    }
}

void Theory_combination::on_learned_clause(Database& db, Trail& trail, Clause const& learned)
{
    for (auto& theory : theories)
    {
        theory->on_learned_clause(db, trail, learned);
    }
}

void Theory_combination::on_conflict_resolved(Database& db, Trail& trail, Clause const& other)
{
    for (auto& theory : theories)
    {
        theory->on_conflict_resolved(db, trail, other);
    }
}

void Theory_combination::on_restart(Database& db, Trail& trail)
{
    for (auto& theory : theories)
    {
        theory->on_restart(db, trail);
    }
}

} // namespace perun