#ifndef YAGA_LINEAR_ARITHMETIC_H
#define YAGA_LINEAR_ARITHMETIC_H

#include <algorithm>
#include <cassert>
#include <cmath>
#include <limits>
#include <optional>
#include <ranges>
#include <unordered_map>
#include <vector>

#include "Bounds.h"
#include "Rational.h"
#include "Linear_constraints.h"
#include "Lra_conflict_analysis.h"
#include "Model.h"
#include "Theory.h"
#include "Variable_bounds.h"

namespace yaga {

class Linear_arithmetic final : public Theory {
public:
    // bounds object which keeps implied bounds of variables
    using Bounds_type = Variable_bounds<Rational>;
    // models relevant to this theory
    using Models = Theory_models<Rational>;
    // type of linear constraints
    using Constraint = Linear_constraint<Rational>;
    // type of the repository that stores linear constraints
    using Constraint_repository = Linear_constraints<Rational>;

    struct Options {
        /** Derive new bounds using FM elimination
         */
        bool prop_bounds = false;

        /** Propagate unassigned linear constraints when they become true due to assignment of 
         * real variables or due to variable bounds.
         */
        bool prop_unassigned = false;

        /** If true, propagate() returns all conflicts derived at current decision level. 
         * Otherwise, only the first conflict is returned.
         */
        bool return_all_conflicts = true;

        /** If true, the plugin will track effectively decided variables.
         * 
         * A rational variable is effectively decided if it can only be assigned one value.
         */
        bool prop_rational = false;
    };

    virtual ~Linear_arithmetic() = default;

    /** Allocate memory for @p num_vars variables of type @p type
     *
     * @param type type of variables
     * @param num_vars new number of variables of type @p type
     */
    void on_variable_resize(Variable::Type type, int num_vars) override;

    /** Add all semantic propagations to the @p trail and update variable bounds
     *
     * @param db clause database
     * @param trail current solver trail
     * @return list of conflict clauses if there exists a real variable that cannot be assigned
     * any value. Empty list, otherwise.
     */
    std::vector<Clause> propagate(Database&, Trail&) override;

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
    Constraint constraint(Trail& trail, Var_range&& vars, Coef_range&& coef,
                          Order_predicate pred, Rational const& rhs)
    {
        // create the constraint
        auto cons = constraints.make(std::forward<Var_range>(vars), std::forward<Coef_range>(coef),
                                     pred, rhs);

        // create a new variable in trail if the constraint represents a new variable
        auto models = relevant_models(trail);
        if (is_new(models, cons.lit().var()))
        {
            if (options.prop_bounds || options.prop_unassigned)
            {
                for (auto var : cons.vars())
                {
                    occur[var].push_back(cons.lit().is_negation() ? ~cons : cons);
                }
            }
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
    [[nodiscard]] inline Bounds_type& find_bounds(int lra_var_ord) { return bounds[lra_var_ord]; }

    /** Get models relevant to this theory
     *
     * @param trail current solver trail
     * @return models from @p trail relevant to this theory
     */
    [[nodiscard]] inline Models relevant_models(Trail& trail) const
    {
        return {trail.model<bool>(Variable::boolean), trail.model<Rational>(Variable::rational)};
    }

    /** Get constraint which implements @p bool_var_ord
     *
     * @param bool_var_ord ordinal number of a boolean variable
     * @return constraint which implements the boolean variable @p bool_var_ord
     */
    inline Constraint constraint(int bool_var_ord) { return constraints[bool_var_ord]; }

    /** Find linear constraint which is defined by @p lit
     *
     * @param lit literal
     * @return constraint represented by @p lit or an empty constraint if @p lit does not
     * represent a linear constraint.
     */
    inline Constraint constraint(Literal lit)
    {
        auto cons = constraint(lit.var().ord());
        if (cons.empty())
        {
            return cons;
        }
        return cons.lit() != lit ? ~cons : cons;
    }

    /** Set options
     * 
     * @param opts new options
     */
    inline void set_options(Options const& opts) { options = opts; }

    /** Check whether @p lra_var_ord can be assigned exactly one value.
     * 
     * @param models current (partial) assignment of variables
     * @param lra_var_ord ordinal number of a variable
     * @return true iff @p lra_var_ord is unassigned and it can be assigned exactly one value
     */
    [[nodiscard]] bool is_effectively_decided(Models const& models, int lra_var_ord);

    /** Get all rational variables with only one allowed value since the last call.
     * 
     * @return list of rational variables that can only be assigned one value.
     */
    inline std::vector<int> effectively_decided()
    {
        auto result = std::move(decided);
        decided.clear();
        return result;
    }
private:
    struct Watched_constraint {
        // watched constraint
        Constraint constraint;
        // index of the next variable to check in `constraint`
        int index;

        inline Watched_constraint(Constraint const& cons)
            : constraint(cons), index(std::min<int>(2, cons.size() - 1))
        {
        }
    };

    // repository of managed linear constraints
    Constraint_repository constraints;
    // map real variable -> list of constraints in which it is watched
    std::vector<std::vector<Watched_constraint>> watched;
    // map real variable -> set of allowed values
    Bounds bounds;
    // cached assignment of LRA variables
    Model<Rational> cached_values;
    // list of rational variables whose bound has changed at this level
    std::vector<int> to_check;
    // map real variable -> list of constraints in which it occurs
    std::vector<std::vector<Constraint>> occur;
    // parameters of optional features
    Options options;
    // unassigned rational variables with only one allowed value
    std::vector<int> decided;

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
     */
    void replace_watch(Trail& trail, Models& models, int lra_var_ord);

    /** Check if some value can be assigned to @p var_ord
     * 
     * If there is a conflict, new constraints can be propagated to @p trail
     *
     * @param trail current solver trail
     * @param var_ord variable to check
     * @return conflict clause if @p var_ord cannot be assigned any value. None, otherwise.
     */
    [[nodiscard]] std::optional<Clause> check_bounds(Trail& trail, int var_ord);

    /** Update bounds implied by a new unit constraint @p cons
     *
     * @param models partial assignment of variables
     * @param cons new unit constraint
     */
    void unit(Models const& models, Constraint const& cons);

    /** Deduce new bounds using bounds added at this decision level
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     */
    void propagate_bounds(Trail const& trail, Models const& models);

    /** Propagate true constraints to the trail
     *
     * @param trail current solver trail
     * @param models partial assignment of variables
     */
    void propagate_unassigned(Trail& trail, Models& models);

    /** Finish propagation by checking if there are any conflicts.
     *
     * @param trail current solver trail
     * @return conflict clauses or an empty list if there are no conflicts.
     */
    std::vector<Clause> finish(Trail& trail);

    /** Check if @p cons is unit (i.e., exactly one variable is unassigned)
     *
     * @param model partial assignment of variables in trail
     * @param cons queried linear constraint
     * @return true iff @p cons is unit constraint
     */
    [[nodiscard]] bool is_unit(Model<Rational> const& model, Constraint const& cons) const;

    /** Check if all variables in @p cons are assigned.
     *
     * @param model partial assignment of variables in trail
     * @param cons queries linear constraint
     * @return true iff all variables in @p cons are assigned.
     */
    [[nodiscard]] bool is_fully_assigned(Model<Rational> const& model,
                                         Constraint const& cons) const;

    /** Find the highest decision level of any assigned variable in @p cons including the boolean
     * variable which represents @p cons (i.e., `cons.lit().var()`)
     *
     * @param trail solver trail
     * @param cons linear constraint
     * @return the highest decision level of any variable in @p cons including the boolean variable
     * which represents @p cons or 0 if no variable is assigned in @p cons
     */
    [[nodiscard]] int decision_level(Trail const& trail, Constraint const& cons) const;

    /** Check if @p var is in @p models
     *
     * @param models partial assignment of variables
     * @param var checked variables
     * @return true iff @p var is in @p models
     */
    [[nodiscard]] bool is_new(Models const& models, Variable var) const;

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
    [[nodiscard]] std::optional<Rational> find_integer(Models const& models, Bounds_type& bounds);

    /** Check that bounds is consistent with all unit constraints on the trail
     *
     * @param trail solver trail
     * @param models partial assignment of variables in @p trail
     */
    void check_bounds_consistency(Trail const& trail, Models const& models);

    /** Check that watched variables are in watch lists
     *
     * @param models partial assignment of variables
     */
    void check_watch_consistency(Models const& models);
};

} // namespace yaga

#endif // YAGA_LINEAR_ARITHMETIC_H