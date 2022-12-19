#ifndef PERUN_CONFLICT_ANALYSIS_H_
#define PERUN_CONFLICT_ANALYSIS_H_

#include <tuple>
#include <vector>
#include <algorithm>
#include <unordered_set>
#include <optional>
#include <cassert>
#include <cstdint>
#include <concepts>

#include "Clause.h"
#include "Trail.h"

namespace perun {

class Conflict_analysis {
public:
    /** Derive a conflict clause suitable for backtracking using resolution.
     * 
     * Postcondition: Literals in the returned clause are ordered by decision level from the highest 
     * to the smallest.
     * 
     * @tparam Resolve_callback function which takes a clause reference as a parameter
     * @param trail current trail 
     * @param conflict conflict clause -- clause that is false in @p trail
     * @param on_resolve callback called for each clause that is resolved with @p conflict 
     * @return conflict clause suitable for backtracking and decision level to backtrack to.
     */
    template<std::invocable<const Clause&> Resolve_callback>
    std::pair<Clause, int> analyze(const Trail& trail, Clause&& conflict, Resolve_callback&& on_resolve)
    {
        // TODO: handle a semantic split correctly
        const auto& model = trail.model<bool>(Variable::boolean);
        assert(eval(model, conflict) == false);

        init(trail, conflict);

        const auto& assigned = trail.assigned(top_level_);
        for (auto it = assigned.rbegin(); !can_backtrack() && it != assigned.rend(); ++it)
        {
            auto [var, reason] = *it;
            if (var.type() == Variable::boolean && reason != nullptr)
            {
                auto lit = model.value(var.ord()) ? Literal{var.ord()}.negate() : Literal{var.ord()};
                if (can_resolve(lit))
                {
                    on_resolve(*reason);
                    resolve(trail, *reason, lit);
                }
            }
        }

        return finish(trail);
    }

    inline std::pair<Clause, int> analyze(const Trail& trail, Clause&& conflict) 
    { 
        return analyze(trail, std::move(conflict), [](const auto&){}); 
    }

private:
    // TODO: use some open addressing implementation?
    // current conflict clause
    std::unordered_set<Literal, Literal_hash> conflict_;
    // the highest decision level in current conflict clause
    int top_level_;
    // number of literals at the `top_level_` in current conflict clause
    int num_top_level_;

    // check if solver can backtrack with current conflict clause
    inline bool can_backtrack() const { return num_top_level_ == 1 && conflict_.size() > 1; }
    // check if current conflict clause contains lit
    inline bool can_resolve(Literal lit) const { return conflict_.contains(lit); }
    // initialize current conflict clause
    void init(const Trail& trail, const Clause& conflict);
    // resolve current conflict with other clause using literal lit (precondition: can_resolve(lit))
    void resolve(const Trail& trail, const Clause& other, Literal lit);
    // finish the conflict derivation
    std::pair<Clause, int> finish(const Trail& trail) const;
};

}

#endif // PERUN_CONFLICT_ANALYSIS_H_