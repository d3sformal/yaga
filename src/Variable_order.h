#ifndef PERUN_VARIABLE_ORDER_H_
#define PERUN_VARIABLE_ORDER_H_

#include "Clause.h"
#include "Database.h"
#include "Trail.h"
#include "Variable.h"

namespace perun {

class Variable_order {
public:
    virtual ~Variable_order() = default;

    virtual void on_init(Database&, Trail&) {}
    virtual void on_variable_resize(Variable::Type, int) {}
    virtual void on_learned_clause(Database&, Trail&, Clause*) {}
    virtual void on_conflict_resolved(Database&, Trail&, const Clause&) {}

    /** Pick an unassigned variable in @p trail to decide
     * 
     * @param db clause database
     * @param trail current trail
     * @return an unassigned variable in @p trail or none if all variables are assigned
     */
    virtual std::optional<Variable> pick(Database&, Trail&) = 0;
};

}

#endif // PERUN_VARIABLE_ORDER_H_