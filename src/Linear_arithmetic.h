#ifndef PERUN_LINEAR_ARITHMETIC_H
#define PERUN_LINEAR_ARITHMETIC_H

#include <algorithm>
#include <cassert>
#include <cmath>
#include <limits>
#include <optional>
#include <ranges>
#include <unordered_map>
#include <vector>

#include "Bounds.h"
#include "Linear_constraints.h"
#include "Model.h"
#include "Theory.h"

namespace perun {

class Linear_arithmetic final : public Theory {
public:
    using Value_type = double;
    using Bounds_type = Bounds<Value_type>;
    using Constraint_type = Linear_constraint<Value_type>;
    using Constraint_repository = Linear_constraints<Value_type>;

    virtual ~Linear_arithmetic() = default;

    /** Allocate memory for @p num_vars variables of type @p type
     *
     * @param type type of variables
     * @param num_vars new number of variables of type @p type
     */
    void on_variable_resize(Variable::Type type, int num_vars) override;

    /** Add all semantic propagations to the @p trail
     *
     * @param db clause database
     * @param trail current solver trail
     * @return conflict clause if there exists a real variable that cannot be assigned any value.
     * None, otherwise.
     */
    std::optional<Clause> propagate(Database&, Trail&) override;

    /** Decide value for @p variable if it is a real variable and add it to the trail.
     *
     * @param db clause database
     * @param trail current solver trail
     * @param variable any variable (not necessarily a real variable)
     */
    void decide(Database&, Trail&, Variable) override;

    /** Create a constraint from @p args or return an existing object that represents the same
     * constraint.
     *
     * @tparam Args types of arguments passed to `Linear_constraints::make`
     * @param args arguments passed to `Linear_constraints::make`
     * @return literal that represents the linear constraint
     */
    template <typename... Args> inline Constraint_type constraint(Args&&... args)
    {
        auto cons = constraints.make(std::forward<Args>(args)...);
        watch(cons);
        return cons;
    }

    /** Get current implied upper and lower bound
     *
     * @param model partial assignment of LRA variables
     * @param lra_var_ord ordinal number of a real variable
     * @return lower and upper bound for @p lra_var_ord
     */
    inline std::pair<Implied_value<Value_type>, Implied_value<Value_type>>
    find_bounds(Model<Value_type> const& model, int lra_var_ord)
    {
        return {bounds[lra_var_ord].lower_bound(model), bounds[lra_var_ord].upper_bound(model)};
    }

private:
    // repository of managed linear constraints
    Constraint_repository constraints;
    // map real variable -> list of constraints in which it is watched
    std::vector<std::vector<Constraint_type>> watched;
    // map real variable -> set of allowed values
    std::vector<Bounds<Value_type>> bounds;

    /** Start watching LRA variables in @p cons
     *
     * @param cons new constraint
     * @param model current partial assignment of LRA variables
     */
    void watch(Constraint_type& cons, Model<Value_type> const& model);

    /** Start watching LRA variables in @p cons assuming the frist two variables in @p cons are
     * unassigned.
     *
     * @param cons new constraint
     */
    void watch(Constraint_type& cons);

    /** Create a constraint from @p args and initialzie watched variables in the constraint
     *
     * @tparam Args types of arguments passed to `Linear_constraints::make`
     * @param model current partial assignment of LRA variables
     * @param args arguments passed to `Linear_constraints::make`
     * @return literal that represents the linear constraint
     */
    template <typename... Args>
    inline Constraint_type constraint(Model<Value_type> const& model, Args&&... args)
    {
        auto cons = constraints.make(std::forward<Args>(args)...);
        watch(cons, model);
        return cons;
    }

    /** Try to replace @p lra_var_ord in watched variables of @p cons
     *
     * @param model partial assignment of LRA variables
     * @param cons linear constraint to update
     * @param lra_var_ord ordinal number of a watched variable in @p cons to replace
     * @return true iff @p lra_var_ord has been replaced
     */
    bool replace_watch(Model<Value_type> const& model, Constraint_type& cons, int lra_var_ord);

    /** Stop watching @p lra_var_ord in all constraints.
     *
     * It detects unit constraints/fully assigned constraints and acts appropriately:
     * -# Unit constraints: the implied bound is propagated to `bounds`.
     * -# Fully-assigned constraints: the corresponding literal is propagated to the @p trail
     * -# Unit constraint of the type `x == c`: `x` is added to the @p assigned stack
     *
     * @param assigned stack with assigned variables (add only)
     * @param trail current solver trail
     * @param bool_model partial assignment of boolean variables
     * @param lra_model partial assignment of real variables
     * @param lra_var_ord newly assigned LRA variable
     * @return conflict clause if a conflict is detected. None, otherwise.
     */
    std::optional<Clause> replace_watch(std::vector<int>& assigned, Trail& trail,
                                        Model<bool>& bool_model, Model<Value_type>& lra_model,
                                        int lra_var_ord);

    /** Update bounds using unit constraint @p cons
     *
     * @param bool_model partial assignment of boolean variables
     * @param lra_model partial assignment of real variables
     * @param cons unit constraint
     */
    void update_bounds(Model<bool> const& bool_model, Model<Value_type> const& lra_model,
                       Constraint_type& cons);

    /** Check if @p bounds is empty (i.e., no value can be assigned to a variable)
     *
     * @param trail current solver trail
     * @param bool_model partial assignment of boolean variables
     * @param lra_model partial assignment of LRA variables
     * @param bounds bounds object to check
     * @return conflict clause if @p bounds is empty. None, otherwise.
     */
    std::optional<Clause> check_bounds(Trail& trail, Model<bool>& bool_model,
                                       Model<Value_type> const& lra_model,
                                       Bounds<Value_type>& bounds);

    /** Check if @p bounds implies an equality (i.e., `L <= x <= U`  and `L = U`)
     *
     * @param lra_model partial assignment of LRA variables
     * @param bounds bounds object to check
     * @return implied constant if @p bounds implies that `x == constant`. None, otherwise.
     */
    std::optional<Value_type> check_equality(Model<Value_type> const& lra_model,
                                             Bounds<Value_type>& bounds);

    /** Report a new unit constraint @p cons and check for conflicts/implied values.
     *
     * If the set of appropriate values for the unassigned variable in @p cons becomes empty, this
     * method returns a conflict. If the set becomes a singleton (i.e., exactly one value is
     * permitted), it is propagated to @p trail
     *
     * @param assigned stack with assigned variables (add only if bounds for the unassigned variable
     * imply an equality)
     * @param trail current solver trail
     * @param bool_model partial assignment of boolean variables
     * @param cons new unit constraint
     */
    std::optional<Clause> unit(std::vector<int>& assigned, Trail& trail, Model<bool>& bool_model,
                               Model<Value_type>& lra_model, Constraint_type& cons);

    /** Check if there is a bound conflict (i.e., `L <= x && x <= U` and `U < L` or similar
     * conflicts with strict bounds)
     *
     * @param trail current solver trail
     * @param bool_model partial assignment of boolean variables
     * @param lra_model partial assignment of real variables
     * @param bounds implied bounds for a variable
     * @return conflict clause if a conflict is detected. None, otherwise.
     */
    std::optional<Clause> check_bound_conflict(Trail& trail, Model<bool>& bool_model,
                                               Model<Value_type> const& lra_model,
                                               Bounds<Value_type>& bounds);

    /** Check if there is an inequality conflict (i.e., `L <= x && x <= U` and `L = U` and `x != L`)
     *
     * @param bool_model partial assignment of boolean variables
     * @param lra_model partial assignment of real variables
     * @param bounds implied bounds for a variable
     * @return conflict clause if a conflict is detected. None, otherwise.
     */
    std::optional<Clause> check_inequality_conflict(Model<bool> const& bool_model,
                                                    Model<Value_type> const& lra_model,
                                                    Bounds<Value_type>& bounds);

    /** Check whether the unit constraint @p cons implies an equality for the only unassigned
     * variable (e.g., `x == 5`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an equality
     */
    bool implies_equality(Constraint_type const& cons) const;

    /** Check whether the unit constraint @p cons implies an inequality for the only unassigned
     * variable (e.g., `x != 4`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an inequality
     */
    bool implies_inequality(Constraint_type const& cons) const;

    /** Check whether the unit constraint @p cons implies a lower bound for the only unassigned
     * variable (e.g., `x > 0`, or `x >= 0`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies a lower bound
     */
    bool implies_lower_bound(Constraint_type const& cons) const;

    /** Check whether the unit constraint @p cons implies an upper bound for the only unassigned
     * variable (e.g., `x < 0`, or `x <= 0`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an upper bound
     */
    bool implies_upper_bound(Constraint_type const& cons) const;

    /** Propagate a fully assigned constraint @p cons to @p trail
     *
     * @param trail current solver trail
     * @param bool_model partial assignment of boolean variables
     * @param lra_model partial assignment of real variables
     * @param cons linear constraint to propagate
     */
    void propagate(Trail& trail, Model<bool>& bool_model, Model<Value_type> const& lra_model,
                   Constraint_type const& cons);

    inline bool is_unit(Model<Value_type> const& model, Constraint_type const& cons) const
    {
        assert(!model.is_defined(cons.vars().front()));
        return cons.size() == 1 || (cons.size() > 1 && model.is_defined(cons.vars()[1]));
    }
};

} // namespace perun

#endif // PERUN_LINEAR_ARITHMETIC_H