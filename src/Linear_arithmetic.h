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
    // types of variable values
    using Value_type = double;
    // bound object that keeps bounds of variables
    using Bounds_type = Bounds<Value_type>;
    // models relevant to this theory
    using Models_type = Theory_models<Value_type>;
    // type of linear constraints
    using Constraint_type = Linear_constraint<Value_type>;
    // type of the repository that stores linear constraints
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

    /** Create a constraint or return an existing object that represents the same constraint.
     *
     * Precondition: the frist two variables in @p vars are unassigned.
     *
     * @tparam Var_range range of LRA variable numbers (ints)
     * @tparam Coef_range range of coefficients (Value_types)
     * @param trail current solver trail
     * @param vars range of LRA variable numbers
     * @param coef range of coefficints of @p vars
     * @param pred predicate of the constraint
     * @param rhs constant on the right-hand-side of the constraint
     * @return linear constraint
     */
    template <std::ranges::range Var_range, std::ranges::range Coef_range>
    inline Constraint_type constraint(Trail& trail, Var_range&& vars, Coef_range&& coef, 
                                      Order_predicate pred, Value_type rhs)
    {
        // create the constraint
        auto cons = constraints.make(std::forward<Var_range>(vars), std::forward<Coef_range>(coef),
                                     pred, rhs);

        // add its boolean variable to trail if it represents a new variable
        auto models = relevant_models(trail);
        if (is_new(models, cons.lit().var()))
        {
            add_variable(trail, models, cons.lit().var());
            watch(cons, models.owned());
        }
        return cons;
    }

    /** Get current implied upper and lower bound
     *
     * @param models partial assignment of variables
     * @param lra_var_ord ordinal number of a real variable
     * @return lower and upper bound for @p lra_var_ord
     */
    inline std::pair<Implied_value<Value_type>, Implied_value<Value_type>>
    find_bounds(Models_type const& models, int lra_var_ord)
    {
        return {bounds[lra_var_ord].lower_bound(models), bounds[lra_var_ord].upper_bound(models)};
    }

    /** Get models relevent to this theory
     *
     * @param trail current solver trail
     * @return models from @p trail relevant to this theory
     */
    inline Models_type relevant_models(Trail& trail) const
    {
        return {&trail.model<bool>(Variable::boolean),
                &trail.model<Value_type>(Variable::rational)};
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
     * @param models partial assignment of variables
     * @param lra_var_ord newly assigned LRA variable
     * @return conflict clause if a conflict is detected. None, otherwise.
     */
    std::optional<Clause> replace_watch(std::vector<int>& assigned, Trail& trail,
                                        Models_type& models, int lra_var_ord);

    /** Update bounds using unit constraint @p cons
     *
     * @param models partial assignment of variables
     * @param cons unit constraint
     */
    void update_bounds(Models_type const& models, Constraint_type& cons);

    /** Check if @p bounds is empty (i.e., no value can be assigned to a variable)
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     * @param bounds bounds object to check
     * @return conflict clause if @p bounds is empty. None, otherwise.
     */
    std::optional<Clause> check_bounds(Trail& trail, Models_type& models,
                                       Bounds<Value_type>& bounds);

    /** Check if @p bounds implies an equality (i.e., `L <= x <= U`  and `L = U`)
     *
     * @param models partial assignment of variables
     * @param bounds bounds object to check
     * @return implied constant if @p bounds implies that `x == constant`. None, otherwise.
     */
    std::optional<Value_type> check_equality(Models_type const& models, Bounds<Value_type>& bounds);

    /** Report a new unit constraint @p cons and check for conflicts/implied values.
     *
     * If the set of appropriate values for the unassigned variable in @p cons becomes empty, this
     * method returns a conflict. If the set becomes a singleton (i.e., exactly one value is
     * permitted), it is propagated to @p trail
     *
     * @param assigned stack with assigned variables (add only if bounds for the unassigned variable
     * imply an equality)
     * @param trail current solver trail
     * @param models partial assignment of variables
     * @param cons new unit constraint
     */
    std::optional<Clause> unit(std::vector<int>& assigned, Trail& trail, Models_type& models,
                               Constraint_type& cons);

    /** Combine @p first and @p second using Fourier-Motzking elimination of the first unassigned 
     * variable in @p first and @p second
     * 
     * Precondition: the first variable in both @p first and @p second is the only unassigned variable 
     * in either constraint.
     * 
     * @param trail current solver trail
     * @param first first constraint
     * @param second second constraint
     * @return Constraint_type 
     */
    Constraint_type eliminate(Trail& trail, Constraint_type const& first, Constraint_type const& second);

    /** Check if there is a bound conflict (i.e., `L <= x && x <= U` and `U < L` or similar
     * conflicts with strict bounds)
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     * @param bounds implied bounds for a variable
     * @return conflict clause if a conflict is detected. None, otherwise.
     */
    std::optional<Clause> check_bound_conflict(Trail& trail, Models_type& models,
                                               Bounds<Value_type>& bounds);

    /** Check if there is an inequality conflict (i.e., `L <= x && x <= U` and `L = U` and `x != L`)
     *
     * @param models partial assignment of variables
     * @param bounds implied bounds for a variable
     * @return conflict clause if a conflict is detected. None, otherwise.
     */
    std::optional<Clause> check_inequality_conflict(Trail& trail, Models_type& models,
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
     * @param models partial assignment of variables
     * @param cons linear constraint to propagate
     */
    void propagate(Trail& trail, Models_type& models, Constraint_type const& cons);

    /** Check if @p var is in @p models
     * 
     * @param models partial assignment of variables
     * @param var checked variables
     * @return true iff @p var is in @p models
     */
    bool is_new(Models_type const& models, Variable var) const;

    /** Add a new boolean variable @p bool_var_ord if @p trail does not already contain such variable.
     * 
     * @param trail current solver trail
     * @param models partial assignment of variables in @p trail
     * @param var variable to add if it is not already in @p trail
     */
    void add_variable(Trail& trail, Models_type const& models, Variable var);

    inline bool is_unit(Model<Value_type> const& model, Constraint_type const& cons) const
    {
        assert(!model.is_defined(cons.vars().front()));
        return cons.size() == 1 || (cons.size() > 1 && model.is_defined(cons.vars()[1]));
    }
};

} // namespace perun

#endif // PERUN_LINEAR_ARITHMETIC_H