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
#include "Fraction.h"
#include "Linear_constraints.h"
#include "Model.h"
#include "Theory.h"

namespace perun {

class Linear_arithmetic final : public Theory {
public:
    // types of variable values
    using Value_type = Fraction<int>;
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

    /** Cache current values of LRA variables on conflict
     *
     * @param db clause database
     * @param trail current solver trail
     * @param learned newly learned clause
     */
    void on_learned_clause(Database& db, Trail& trail, Clause const& learned) override;

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
     * @tparam Var_range range of LRA variable numbers (ints)
     * @tparam Coef_range range of coefficients (Value_types)
     * @param trail current solver trail
     * @param vars range of LRA variable numbers
     * @param coef range of coefficients of @p vars
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

        // create a new variable in trail if the constraint represents a new variable
        auto models = relevant_models(trail);
        if (is_new(models, cons.lit().var()))
        {
            add_variable(trail, models, cons.lit().var());
            watch(cons, models.owned());
        }
        return cons;
    }

    /** Get current implied bounds for @p lra_var_ord
     *
     * @param lra_var_ord ordinal number of a real variable
     * @return implied bounds for @p lra_var_ord
     */
    inline Bounds_type& find_bounds(int lra_var_ord) { return bounds[lra_var_ord]; }

    /** Get models relevant to this theory
     *
     * @param trail current solver trail
     * @return models from @p trail relevant to this theory
     */
    inline Models_type relevant_models(Trail& trail) const
    {
        return {&trail.model<bool>(Variable::boolean),
                &trail.model<Value_type>(Variable::rational)};
    }

    /** Get constraint which implements @p bool_var_ord
     *
     * @param bool_var_ord ordinal number of a boolean variable
     * @return constraint which implements the boolean variable @p bool_var_ord
     */
    inline Constraint_type constraint(int bool_var_ord) { return constraints[bool_var_ord]; }

private:
    // repository of managed linear constraints
    Constraint_repository constraints;
    // map real variable -> list of constraints in which it is watched
    std::vector<std::vector<Constraint_type>> watched;
    // map real variable -> set of allowed values
    std::vector<Bounds<Value_type>> bounds;
    // cached assignment of LRA variables
    Model<Value_type> cached_values;

    /** Convert @p value to integer
     *
     * @param value value to convert
     * @return integer part of @p value
     * @return integer value closest to @p value if @p value does not have a representation as an
     * int
     */
    int convert(Value_type value) const;

    /** Start watching LRA variables in @p cons
     *
     * @param cons new constraint
     * @param model current partial assignment of LRA variables
     */
    void watch(Constraint_type& cons, Model<Value_type> const& model);

    /** Start watching LRA variables in @p cons assuming the first two variables in @p cons are
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
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     * @param lra_var_ord newly assigned LRA variable
     * @return conflict clause if a conflict is detected. None, otherwise.
     */
    std::optional<Clause> replace_watch(Trail& trail, Models_type& models, int lra_var_ord);

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
    std::optional<Clause> check_bounds(Trail& trail, Models_type& models, Bounds_type& bounds);

    /** Check if @p bounds implies an equality (i.e., `L <= x <= U`  and `L = U`)
     *
     * @param models partial assignment of variables
     * @param bounds bounds object to check
     * @return implied constant if @p bounds implies that `x == constant`. None, otherwise.
     */
    std::optional<Value_type> check_equality(Models_type const& models, Bounds_type& bounds);

    /** Report a new unit constraint @p cons and check for conflicts.
     *
     * If the unassigned variable in @p cons cannot be assigned any value, this method returns a
     * conflict clause.
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     * @param cons new unit constraint
     */
    std::optional<Clause> unit(Trail& trail, Models_type& models, Constraint_type& cons);

    /** Group elements in @p polynomial by variable and sum up coefficients in each group.
     *
     * This method also drops variables whose coefficient becomes 0.
     *
     * @param polynomial polynomial to normalize
     */
    void group_by_variable(std::vector<std::pair<int, Value_type>>& polynomial);

    /** Combine @p first and @p second using Fourier-Motzkin elimination of the first unassigned
     * variable in @p first and @p second
     *
     * Precondition: the first variable in both @p first and @p second is the only unassigned
     * variable in both constraints.
     *
     * @param trail current solver trail
     * @param first first constraint
     * @param second second constraint
     * @return Fourier-Motzkin derivation from @p first and @p second
     */
    Constraint_type eliminate(Trail& trail, Constraint_type const& first,
                              Constraint_type const& second);

    /** Check if there is a bound conflict (i.e., `L <= x && x <= U` and `U < L` or similar
     * conflicts with strict bounds)
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     * @param bounds implied bounds for a variable
     * @return conflict clause if a bound conflict is detected. None, otherwise.
     */
    std::optional<Clause> check_bound_conflict(Trail& trail, Models_type& models,
                                               Bounds_type& bounds);

    /** Check if there is an inequality conflict (i.e., `L <= x && x <= U` and `L = U` and `x != L`)
     *
     * @param models partial assignment of variables
     * @param bounds implied bounds for a variable
     * @return conflict clause if a conflict is detected. None, otherwise.
     */
    std::optional<Clause> check_inequality_conflict(Trail& trail, Models_type& models,
                                                    Bounds_type& bounds);

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
     * Precondition: @p cons (its boolean variable) is not on the trail
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

    /** Allocate space for a new variable @p var in @p trail if it is necessary.
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