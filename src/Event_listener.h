#ifndef PERUN_EVENT_LISTENER_H_
#define PERUN_EVENT_LISTENER_H_

#include "Database.h"
#include "Trail.h"
#include "Clause.h"

namespace perun {

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

    /** Called when a new clause is learned and added to @p db
     * 
     * @param db clause database
     * @param trail current solver trail
     * @param learned pointer to the newly learned clause in @p db
     */
    virtual void on_learned_clause(Database&, Trail&, Clause*) {}

    /** Called when a conflict clause is resolved with @p other_clause in conflict analysis
     * 
     * @param db clause database
     * @param trail current solver trail
     * @param other_clause clause that is resolved with current conflict clause
     */
    virtual void on_conflict_resolved(Database&, Trail&, const Clause&) {}

    /** Called when a conflict clause is derived by conflict analysis (before 
     * `on_learend_clause()`)
     * 
     * Implementations are free to modify the @p conflict clause
     * 
     * @param db clause database without @p conflict 
     * @param trail current solver trail
     * @param conflict clause that is false in @p trail
     */
    virtual void on_conflict_derived(Database&, Trail&, Clause&) {}

    /** Called after each restart
     * 
     * @param db clause database
     * @param trail current solver trail after restart
     */
    virtual void on_restart(Database&, Trail&) {}
};

}

#endif // PERUN_EVENT_LISTENER_H_