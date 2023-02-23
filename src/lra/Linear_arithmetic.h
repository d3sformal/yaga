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

#include "Arithmetic_conflict_analysis.h"
#include "Bounds.h"
#include "Fraction.h"
#include "Linear_constraints.h"
#include "Model.h"
#include "Theory.h"

namespace perun {

class Linear_arithmetic final : public Theory {
public:
    // types of variable values
    using Rational = Fraction<int>;
    // bounds object which keeps implied bounds of variables
    using Variable_bounds = Bounds<Rational>;
    // models relevant to this theory
    using Models = Theory_models<Rational>;
    // type of linear constraints
    using Constraint = Linear_constraint<Rational>;
    // type of the repository that stores linear constraints
    using Constraint_repository = Linear_constraints<Rational>;

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

    /** Propagate a fully assigned constraint @p cons to @p trail
     *
     * Precondition: @p cons (its boolean variable) is not on the trail
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     * @param cons linear constraint to propagate
     */
    void propagate(Trail& trail, Models& models, Constraint const& cons);

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
    inline Constraint constraint(Trail& trail, Var_range&& vars, Coef_range&& coef,
                                 Order_predicate pred, Rational rhs)
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
    inline Variable_bounds& find_bounds(int lra_var_ord) { return bounds[lra_var_ord]; }

    /** Get models relevant to this theory
     *
     * @param trail current solver trail
     * @return models from @p trail relevant to this theory
     */
    inline Models relevant_models(Trail& trail) const
    {
        return {&trail.model<bool>(Variable::boolean), &trail.model<Rational>(Variable::rational)};
    }

    /** Get constraint which implements @p bool_var_ord
     *
     * @param bool_var_ord ordinal number of a boolean variable
     * @return constraint which implements the boolean variable @p bool_var_ord
     */
    inline Constraint constraint(int bool_var_ord) { return constraints[bool_var_ord]; }

private:
    struct Watched_constraint {
        // watched constraint
        Constraint constraint;
        // index of the next variable to check in `constraint`
        int index;

        inline Watched_constraint(Constraint cons)
            : constraint(cons), index(std::min<int>(2, cons.size() - 1))
        {
        }
    };

    // repository of managed linear constraints
    Constraint_repository constraints;
    // map real variable -> list of constraints in which it is watched
    std::vector<std::vector<Watched_constraint>> watched;
    // map real variable -> set of allowed values
    std::vector<Bounds<Rational>> bounds;
    // cached assignment of LRA variables
    Model<Rational> cached_values;

    /** Start watching LRA variables in @p cons
     *
     * @param cons new constraint
     * @param model current partial assignment of LRA variables
     */
    void watch(Constraint& cons, Model<Rational> const& model);

    /** Start watching LRA variables in @p cons assuming the first two variables in @p cons are
     * unassigned.
     *
     * @param cons new constraint
     */
    void watch(Constraint& cons);

    /** Try to replace @p lra_var_ord in watched variables of @p watch
     *
     * @param model partial assignment of LRA variables
     * @param watch watched linear constraint to update
     * @param lra_var_ord ordinal number of a watched variable in @p watch to replace
     * @return true iff @p lra_var_ord has been replaced
     */
    bool replace_watch(Model<Rational> const& model, Watched_constraint& watch, int lra_var_ord);

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
    std::optional<Clause> replace_watch(Trail& trail, Models& models, int lra_var_ord);

    /** Update bounds using unit constraint @p cons
     *
     * @param models partial assignment of variables
     * @param cons unit constraint
     */
    void update_bounds(Models const& models, Constraint& cons);

    /** Check if @p bounds is empty (i.e., no value can be assigned to a variable)
     *
     * @param trail current solver trail
     * @param bounds bounds object to check
     * @return conflict clause if @p bounds is empty. None, otherwise.
     */
    std::optional<Clause> check_bounds(Trail& trail, Variable_bounds& bounds);

    /** Report a new unit constraint @p cons and check for conflicts.
     *
     * If the unassigned variable in @p cons cannot be assigned any value, this method returns a
     * conflict clause.
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     * @param cons new unit constraint
     */
    std::optional<Clause> unit(Trail& trail, Models& models, Constraint& cons);

    /** Check whether the unit constraint @p cons implies an equality for the only unassigned
     * variable (e.g., `x == 5`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an equality
     */
    bool implies_equality(Constraint const& cons) const;

    /** Check whether the unit constraint @p cons implies an inequality for the only unassigned
     * variable (e.g., `x != 4`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an inequality
     */
    bool implies_inequality(Constraint const& cons) const;

    /** Check whether the unit constraint @p cons implies a lower bound for the only unassigned
     * variable (e.g., `x > 0`, or `x >= 0`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies a lower bound
     */
    bool implies_lower_bound(Constraint const& cons) const;

    /** Check whether the unit constraint @p cons implies an upper bound for the only unassigned
     * variable (e.g., `x < 0`, or `x <= 0`)
     *
     * @param cons linear constraint with exactly one unassigned variable
     * @return true iff @p cons implies an upper bound
     */
    bool implies_upper_bound(Constraint const& cons) const;

    /** Check if @p cons is unit (i.e., exactly one variable is unassigned)
     * 
     * @param model partial assignment of variables in trail
     * @param cons queried linear constraint
     * @return true iff @p cons is unit constraint
     */
    bool is_unit(Model<Rational> const& model, Constraint const& cons) const;

    /** Check if all variables in @p cons are assigned.
     * 
     * @param model partial assignment of variables in trail
     * @param cons queries linear constraint
     * @return true iff all variables in @p cons are assigned.
     */
    bool is_fully_assigned(Model<Rational> const& model, Constraint const& cons) const;

    /** Check if @p var is in @p models
     *
     * @param models partial assignment of variables
     * @param var checked variables
     * @return true iff @p var is in @p models
     */
    bool is_new(Models const& models, Variable var) const;

    /** Allocate space for a new variable @p var in @p trail if it is necessary.
     *
     * @param trail current solver trail
     * @param models partial assignment of variables in @p trail
     * @param var variable to add if it is not already in @p trail
     */
    void add_variable(Trail& trail, Models const& models, Variable var);

    /** Try to find an integer value allowed by @p bounds
     *
     * @param models partial assignment of variables in trail
     * @param bounds implied bounds of a variable
     * @return integer value allowed by @p bounds or none if there is no such value
     */
    std::optional<Rational> find_integer(Models const& models, Variable_bounds& bounds);
};

} // namespace perun

#endif // PERUN_LINEAR_ARITHMETIC_H