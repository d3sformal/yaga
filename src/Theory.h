#ifndef PERUN_THEORY_H_
#define PERUN_THEORY_H_

#include <optional>

#include "Trail.h"
#include "Database.h"
#include "Clause.h"

namespace perun {

/** Plugin interface for theory specific functions.
 */
class Theory {
public:
    virtual ~Theory() = default;

    /** Propagate all unit constraints managed by this theory.
     * 
     * @param db clause database
     * @param trail current trail. All propagations are added to the trail.
     * @return a conflict clause -- clause that is false in @p trail -- if it detects a conflict. 
     * None, otherwise.
     */
    virtual std::optional<Clause> propagate(Database&, Trail&) = 0;

    /** Decide a value for variable @p var
     * 
     * The method should ignore the request if @p var is not owned by this theory.
     * 
     * @param db clause database
     * @param trail current trail
     * @param var variable to decide
     */
    virtual void decide(Database&, Trail&, Variable) = 0;

    /** Event called whenever a new clause is learned.
     * 
     * @param db clause database
     * @param trail current trail
     * @param clause newly learned clause - pointer to @p db 
     */
    virtual void on_learned_clause(Database&, Trail&, Clause*) {}
};

}

#endif // PERUN_THEORY_H_