#ifndef PERUN_VARIABLE_BOUNDS_H
#define PERUN_VARIABLE_BOUNDS_H

#include <algorithm>
#include <cassert>
#include <vector>

#include "Bounds.h"
#include "Fraction.h"
#include "Trail.h"

namespace perun {

/** Type responsible for keeping bounds for all rational variables.
 */
class Variable_bounds {
public:
    using Rational = Fraction<int>;
    using Bounds_type = Bounds<Rational>;
    using Bound = Implied_value<Rational>;
    using Models = Theory_models<Rational>;
    using Constraint = Linear_constraint<Rational>;

    /** Change the number of rational variables
     * 
     * @param num_vars new number of rational variables
     */
    void resize(int num_vars);

    /** Deduce a new bounds from @p cons
     * 
     * @param models partial assignment of variables
     * @param cons constraint used to deduce new bounds
     */
    void deduce(Models const& models, Constraint cons);

    /** Update bounds using the unit constraint @p cons
     * 
     * @param models partial assignment of variables
     * @param cons new unit constraint
     */
    void update(Models const& models, Constraint cons);

    /** Get range of rational variables whose bound has changed since the last call to `changed()`
     * 
     * @return range of variables with updated bounds
     */
    std::vector<int> const& changed();

    /** Check whether an unassigned constraint can be deduced to be true in current trail
     * 
     * @param models partial assignment of variables
     * @param cons checked constraint
     * @return true iff @p cons is true in current trail
     */
    bool is_implied(Models const& models, Constraint cons);

    /** Check whether the unit constraint @p cons implies an equality for the only unassigned
     * variable (e.g., `x == 5`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an equality
     */
    [[nodiscard]] bool implies_equality(Constraint const& cons) const;

    /** Check whether the unit constraint @p cons implies an inequality for the only unassigned
     * variable (e.g., `x != 4`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an inequality
     */
    [[nodiscard]] bool implies_inequality(Constraint const& cons) const;

    /** Check whether the unit constraint @p cons implies a lower bound for the only unassigned
     * variable (e.g., `x > 0`, or `x >= 0`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies a lower bound
     */
    [[nodiscard]] bool implies_lower_bound(Constraint const& cons) const;

    /** Check whether the unit constraint @p cons implies an upper bound for the only unassigned
     * variable (e.g., `x < 0`, or `x <= 0`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an upper bound
     */
    [[nodiscard]] bool implies_upper_bound(Constraint const& cons) const;

    /** Get bounds for a variable @p var
     * 
     * @param var rational variable number
     * @return bounds for @p var
     */
    inline Bounds_type& operator[](int var) { return bounds[var]; }
private:
    // map lra variable ordinal -> bounds for that variable
    std::vector<Bounds_type> bounds;
    // variables with updated bounds
    std::vector<int> updated_read;
    std::vector<int> updated_write;

    /** Check whether @p bound depends on a linear constraint whose boolean variable is @p bool_var
     * 
     * @param bound checked bound
     * @param bool_var ordinal number of a boolean variable
     * @return true iff @p bound depends on @p bool_var
     */
    bool depends_on(Implied_value<Rational> const& bound, int bool_var) const;

};

}

#endif // PERUN_VARIABLE_BOUNDS_H