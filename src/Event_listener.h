#ifndef YAGA_EVENT_LISTENER_H
#define YAGA_EVENT_LISTENER_H

#include "Clause.h"
#include "Database.h"
#include "Trail.h"

namespace yaga {

class Event_listener {
public:
    virtual ~Event_listener() = default;

    /** Called when solver starts a new check
     *
     * @param db clause database
     * @param trail current solver trail
     */
    virtual void on_init(Database&, Trail&) {}

    /** Called when number of variables of type @p type changes
     *
     * @param type type of variables
     * @param num_vars new number of variables
     */
    virtual void on_variable_resize(Variable::Type, int) {}

    /** Called when the solver is about to backtrack to @p decision_level
     *
     * @param db clause database
     * @param trail current solver trail before backtracking
     * @param decision_level decision level to backtrack to
     */
    virtual void on_before_backtrack(Database&, Trail&, int) {}

    /** Called when a new clause is learned and added to @p db
     *
     * @param db clause database
     * @param trail current solver trail
     * @param learned reference to the newly learned clause in @p db
     */
    virtual void on_learned_clause(Database&, Trail&, Clause const&) {}

    /** Called when a conflict clause is resolved with @p other_clause in
     * conflict analysis
     *
     * @param db clause database
     * @param trail current solver trail
     * @param other_clause clause that is resolved with current conflict clause
     */
    virtual void on_conflict_resolved(Database&, Trail&, Clause const&) {}

    /** Called after each restart
     *
     * @param db clause database
     * @param trail current solver trail after restart
     */
    virtual void on_restart(Database&, Trail&) {}
};

} // namespace yaga

#endif // YAGA_EVENT_LISTENER_H