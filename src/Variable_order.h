#ifndef PERUN_VARIABLE_ORDER_H_
#define PERUN_VARIABLE_ORDER_H_

#include "Clause.h"
#include "Database.h"
#include "Trail.h"
#include "Variable.h"
#include "Event_listener.h"

namespace perun {

class Variable_order : public Event_listener {
public:
    virtual ~Variable_order() = default;

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