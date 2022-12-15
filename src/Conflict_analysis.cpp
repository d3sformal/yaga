#include "Conflict_analysis.h"

namespace perun {

void Conflict_analysis::init(const Trail& trail, const Clause& conflict)
{
    top_level_ = 0;
    conflict_.clear();
    for (auto lit : conflict)
    {
        conflict_.insert(lit);
        top_level_ = std::max<int>(top_level_, trail.decision_level(lit.var()).value());
    }

    num_top_level_ = std::count_if(conflict.begin(), conflict.end(), [&](auto lit) {
        return trail.decision_level(lit.var()).value() == top_level_;
    });
}

void Conflict_analysis::resolve(const Trail& trail, const Clause& other, Literal conflict_lit)
{
    assert(can_resolve(conflict_lit));

    for (auto lit : other)
    {
        if (lit != conflict_lit.negate())
        {
            auto[_, is_inserted] = conflict_.insert(lit);
            if (is_inserted && trail.decision_level(lit.var()) == top_level_)
            {
                ++num_top_level_;
            }
        }
    }

    assert(trail.decision_level(conflict_lit.var()) == top_level_);

    conflict_.erase(conflict_.find(conflict_lit));
    --num_top_level_;
}

std::pair<Clause, int> Conflict_analysis::finish(const Trail& trail) const
{
    Clause conflict{conflict_.begin(), conflict_.end()};
    if (conflict.empty())
    {
        return {conflict, -1};
    }

    // move literals with the highest decision level to the front
    std::sort(conflict.begin(), conflict.end(), [&](auto&& lhs, auto&& rhs) {
        return trail.decision_level(lhs.var()).value_or(-1) > trail.decision_level(rhs.var()).value_or(-1);
    });

    // conflict is still false in trail
    assert(!eval(trail, conflict).value_or(true)); 

    return {conflict, conflict.size() <= 1 ? 0 : trail.decision_level(conflict[1].var()).value()};
}

std::optional<bool> Conflict_analysis::eval(const Trail& trail, const Clause& clause) const
{
    const auto& model = trail.model<bool>(Variable::boolean);

    std::size_t num_assigned = 0;
    for (auto lit : clause)
    {
        if (model.is_defined(lit.var().ord()))
        {
            if (model.value(lit.var().ord()) == !lit.is_negation())
            {
                return true;
            }
            ++num_assigned;
        }
    }
    return num_assigned >= clause.size() ? false : std::optional<bool>{};
}

}