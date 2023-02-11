#include "Conflict_analysis.h"

namespace perun {

void Conflict_analysis::init(Trail const& trail, Clause const& clause)
{
    top_level = 0;
    conflict.clear();
    for (auto lit : clause)
    {
        conflict.insert(lit);
        top_level = std::max<int>(top_level, trail.decision_level(lit.var()).value());
    }

    num_top_level = std::count_if(conflict.begin(), conflict.end(), [&](auto lit) {
        return trail.decision_level(lit.var()).value() == top_level;
    });
}

void Conflict_analysis::resolve(Trail const& trail, Clause const& other, Literal conflict_lit)
{
    assert(can_resolve(conflict_lit));

    for (auto lit : other)
    {
        if (lit != conflict_lit.negate())
        {
            auto [_, is_inserted] = conflict.insert(lit);
            if (is_inserted && trail.decision_level(lit.var()) == top_level)
            {
                ++num_top_level;
            }
        }
    }

    assert(trail.decision_level(conflict_lit.var()) == top_level);

    conflict.erase(conflict.find(conflict_lit));
    --num_top_level;
}

std::pair<Clause, int> Conflict_analysis::finish(Trail const& trail) const
{
    Clause clause{conflict.begin(), conflict.end()};
    if (clause.empty())
    {
        return {clause, -1};
    }

    // move literals with the highest decision level to the front
    // this normalizes conflict analysis output regardless of hash set implementation
    std::sort(clause.begin(), clause.end(), [&](auto&& lhs, auto&& rhs) {
        auto lhs_level = trail.decision_level(lhs.var()).value_or(-1);
        auto rhs_level = trail.decision_level(rhs.var()).value_or(-1);
        return lhs_level > rhs_level ||
               (lhs_level == rhs_level && lhs.var().ord() < rhs.var().ord());
    });
    assert(eval(trail.model<bool>(Variable::boolean), clause) == false);

    if (num_top_level >= 2) // if clause is a semantic split
    {
        return {clause, top_level - 1};
    }

    return {clause, clause.size() <= 1 ? 0 : trail.decision_level(clause[1].var()).value()};
}

} // namespace perun