#include "Theory_combination.h"

namespace yaga {

std::vector<Clause> Theory_combination::propagate(Database& db, Trail& trail)
{
    for (;;)
    {
        auto old_size = trail.recent().size();
        for (auto&& theory : theories())
        {
            auto conflicts = theory->propagate(db, trail);
            if (!conflicts.empty())
            {
                return conflicts;
            }
        }

        // if no new propagations were made
        if (old_size == trail.recent().size())
        {
            break;
        }
    }
    return {}; // no conflict
}

void Theory_combination::decide(Database& db, Trail& trail, Variable var)
{
    for (auto&& theory : theories())
    {
        theory->decide(db, trail, var);
    }
}

void Theory_combination::on_init(Database& db, Trail& trail)
{
    for (auto&& theory : theories())
    {
        theory->on_init(db, trail);
    }
}

void Theory_combination::on_before_backtrack(Database& db, Trail& trail, int level)
{
    for (auto&& theory : theories())
    {
        theory->on_before_backtrack(db, trail, level);
    }
}

void Theory_combination::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type >= current_num_vars.size())
    {
        current_num_vars.resize(type + 1);
    }
    current_num_vars[type] = num_vars;

    for (auto&& theory : theories())
    {
        theory->on_variable_resize(type, num_vars);
    }
}

void Theory_combination::on_learned_clause(Database& db, Trail& trail, Clause const& learned)
{
    for (auto&& theory : theories())
    {
        theory->on_learned_clause(db, trail, learned);
    }
}

void Theory_combination::on_conflict_resolved(Database& db, Trail& trail, Clause const& other)
{
    for (auto&& theory : theories())
    {
        theory->on_conflict_resolved(db, trail, other);
    }
}

void Theory_combination::on_restart(Database& db, Trail& trail)
{
    for (auto&& theory : theories())
    {
        theory->on_restart(db, trail);
    }
}

} // namespace yaga