#ifndef YAGA_FIRST_UNASSIGNED_H
#define YAGA_FIRST_UNASSIGNED_H

#include <optional>
#include <ranges>

#include "Database.h"
#include "Trail.h"
#include "Variable.h"
#include "Variable_order.h"

namespace yaga {

/** Pick the first unassigned variable.
 *
 * This is a primitive but predictable heuristic suitable mostly for testing.
 */
class First_unassigned final : public Variable_order {
public:
    virtual ~First_unassigned() = default;

    /** Create a first unassigned variable order for all variables regardless of type.
     */
    inline First_unassigned() {}

    /** Create a first unassigned variable order for variables of specified type only.
     *
     * @param type type of variables considered by this class
     */
    inline explicit First_unassigned(Variable::Type type) : var_type(type) {}

    /** Find the first unassigned variable.
     *
     * @param db clause database
     * @param trail current solver trail
     * @return the first unassigned variable or none if all variables are assigned.
     */
    std::optional<Variable> pick(Database&, Trail&) override;

    /** Check whether @p lhs should be decided before @p rhs
     * 
     * @param lhs first variable
     * @param rhs second variable
     * @return true iff @p lhs should be decided before @p rhs
     */
    bool is_before(Variable lhs, Variable rhs) const override;

private:
    std::optional<Variable::Type> var_type;
};

} // namespace yaga

#endif // YAGA_FIRST_UNASSIGNED_H