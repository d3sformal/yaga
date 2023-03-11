#ifndef PERUN_CONFLICT_ANALYSIS_H
#define PERUN_CONFLICT_ANALYSIS_H

#include <algorithm>
#include <cassert>
#include <concepts>
#include <cstdint>
#include <optional>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "Clause.h"
#include "Trail.h"

namespace perun {

class Conflict_analysis {
public:
    /** Derive a conflict clause suitable for backtracking using resolution.
     *
     * Postcondition: Literals in the returned clause are ordered by decision level from
     * the highest to the smallest.
     *
     * @tparam Resolve_callback function which takes a clause reference as a parameter
     * @param trail current trail
     * @param conflict conflict clause -- clause that is false in @p trail
     * @param on_resolve callback called for each clause that is resolved with @p conflict
     * @return conflict clause suitable for backtracking and decision level to backtrack to.
     */
    template <std::invocable<Clause const&> Resolve_callback>
    std::pair<Clause, int> analyze(Trail const& trail, Clause&& conflict,
                                   Resolve_callback&& on_resolve)
    {
        auto const& model = trail.model<bool>(Variable::boolean);
        assert(eval(model, conflict) == false);

        init(trail, conflict);

        auto const& assigned = trail.assigned(top_level);
        for (auto it = assigned.rbegin(); !can_backtrack() && it != assigned.rend(); ++it)
        {
            auto [var, reason] = *it;
            if (var.type() == Variable::boolean && reason != nullptr)
            {
                auto lit =
                    model.value(var.ord()) ? Literal{var.ord()}.negate() : Literal{var.ord()};
                if (can_resolve(lit))
                {
                    on_resolve(*reason);
                    resolve(trail, *reason, lit);
                }
            }
        }

        return finish(trail);
    }

    inline std::pair<Clause, int> analyze(Trail const& trail, Clause&& conflict)
    {
        return analyze(trail, std::move(conflict), [](auto const&) {});
    }

private:
    // TODO: use some open addressing implementation?
    // current conflict clause
    std::unordered_set<Literal, Literal_hash> conflict;
    // the highest decision level in current conflict clause
    int top_level;
    // number of literals at the `top_level` in current conflict clause
    int num_top_level;

    // check if solver can backtrack with current conflict clause
    inline bool can_backtrack() const { return num_top_level == 1 && conflict.size() > 1; }
    // check if current conflict clause contains lit
    inline bool can_resolve(Literal lit) const { return conflict.contains(lit); }
    // initialize current conflict clause
    void init(Trail const& trail, Clause const& conflict);
    // resolve current conflict with other clause using literal lit
    // (precondition: can_resolve(lit))
    void resolve(Trail const& trail, Clause const& other, Literal lit);
    // finish the conflict derivation
    std::pair<Clause, int> finish(Trail const& trail) const;
};

} // namespace perun

#endif // PERUN_CONFLICT_ANALYSIS_H