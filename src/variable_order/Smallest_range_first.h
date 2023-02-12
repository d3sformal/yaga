#ifndef PERUN_SMALLEST_RANGE_FIRST_H
#define PERUN_SMALLEST_RANGE_FIRST_H

#include <limits>

#include "Linear_arithmetic.h"
#include "Variable.h"
#include "Variable_order.h"

namespace perun {

/** Variable order for LRA variables only which always chooses a variable with the smallest range 
 * of allowed values.
 */
class Smallest_range_first final : public Variable_order {
public:
    virtual ~Smallest_range_first() = default;

    /** Create a new heuristic
     * 
     * @param lra LRA plugin with variable bounds
     */
    inline explicit Smallest_range_first(Linear_arithmetic& lra) : lra(&lra) {}

    /** Find a rational variable with the smallest range of allowed values.
     * 
     * @param db clause database
     * @param trail current solver trail
     * @return LRA variable with the smallest range of allowed values.
     */
    std::optional<Variable> pick(Database&, Trail& trail) override;

private:
    Linear_arithmetic* lra;
};

}

#endif // PERUN_SMALLEST_RANGE_FIRST_H