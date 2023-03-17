#ifndef PERUN_THEORY_H
#define PERUN_THEORY_H

#include <optional>
#include <ranges>

#include "Clause.h"
#include "Database.h"
#include "Event_listener.h"
#include "Trail.h"
#include "Variable.h"

namespace perun {

/** Plugin interface for theory specific functions.
 */
class Theory : public Event_listener {
public:
    virtual ~Theory() = default;

    /** Propagate all unit constraints managed by this theory.
     *
     * @param db clause database
     * @param trail current trail. All propagations are added to the trail.
     * @return conflict clause -- clause that is false in @p trail
     */
    virtual std::vector<Clause> propagate(Database&, Trail&) = 0;

    /** Decide a value for variable @p var
     *
     * The method should ignore the request if @p var is not owned by this
     * theory.
     *
     * @param db clause database
     * @param trail current trail
     * @param var variable to decide
     */
    virtual void decide(Database&, Trail&, Variable) = 0;

    /** Reset the last checked position on the @p trail for the next `assigned()` call
     * 
     * @param db clause database
     * @param trail current solver trail
     * @param level decision level to backtrack to
     */
    void on_before_backtrack(Database&, Trail&, int) override;

protected:
    using Trail_const_iterator = std::vector<Trail::Assignment>::const_iterator;
    using Trail_subrange = std::ranges::subrange<Trail_const_iterator>;

    // the next element to check on trail (in `assigned()`)
    int next_index = 0;
    // current decision level to check whether `next_index` is valid
    int current_level = 0;

    /** Find range of assigned variables on @p trail which have not been processed yet by this 
     * plugin.
     *
     * @param trail current solver trail
     * @return range or assigned, unprocessed elements on the @p trail
     */
    [[nodiscard]] Trail_subrange assigned(Trail const& trail);
};

} // namespace perun

#endif // PERUN_THEORY_H