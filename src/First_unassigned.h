#ifndef PERUN_FIRST_UNASSIGNED_H
#define PERUN_FIRST_UNASSIGNED_H

#include <optional>

#include "Database.h"
#include "Trail.h"
#include "Variable.h"
#include "Variable_order.h"

namespace perun {

/** Pick the first unassigned variable.
 *
 * This is a primitive but predictable heuristic suitable mostly for testing.
 */
class First_unassigned final : public Variable_order {
public:
    virtual ~First_unassigned() = default;

    /** Find the frist unassigned variable of any type.
     *
     * @param db clause database
     * @param trail current solver trail
     * @return the first unassigned variable or none if all variables are assigned.
     */
    std::optional<Variable> pick(Database&, Trail&) override;
};

} // namespace perun

#endif // PERUN_FIRST_UNASSIGNED_H