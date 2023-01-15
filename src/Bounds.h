#ifndef PERUN_BOUNDS_H
#define PERUN_BOUNDS_H

#include <algorithm>
#include <cassert>
#include <limits>
#include <type_traits>
#include <vector>

#include "Linear_constraints.h"
#include "Model.h"

namespace perun {

/** Value implied by a linear constraint
 *
 * @tparam Value_type
 */
template <typename Value_type> class Implied_value {
public:
    using Constraint_type = Linear_constraint<Value_type>;

    inline Implied_value(Value_type val, Constraint_type cons) : val(val), cons(cons) {}

    /** Get the implied value
     *
     * @return implied value
     */
    inline Value_type value() const { return val; }

    /** Get linear constraint that implied this bound.
     *
     * @return pointer to the linear constraint that implied this bound
     */
    inline Constraint_type reason() const { return cons; }

private:
    // implied bound
    Value_type val;
    // linear constraint that implied the bound
    Constraint_type cons;
};

/** Reference to models relevant for a theory
 *
 * @tparam Value type of variables of the theory
 */
template <typename Value> class Theory_models {
public:
    Theory_models(Model<bool>* bool_model, Model<Value>* owned_model)
        : bool_model(bool_model), owned_model(owned_model)
    {
    }

    /** Get model of boolean variables
     *
     * @return partial assignment of boolean variables
     */
    inline Model<bool> const& boolean() const { return *bool_model; }

    /** Get model of boolean variables
     *
     * @return partial assignment of boolean variables
     */
    inline Model<bool>& boolean() { return *bool_model; }

    /** Get model of variables owned by the theory
     *
     * @return partial assignment of variables owned by the theory
     */
    inline Model<Value> const& owned() const { return *owned_model; }

    /** Get model of variables owned by the theory
     *
     * @return partial assignment of variables owned by the theory
     */
    inline Model<Value>& owned() { return *owned_model; }

private:
    Model<bool>* bool_model;
    Model<Value>* owned_model;
};

/** This class keeps track of implied bounds and inequalities for a variable.
 *
 * Obsolete bounds are removed lazily when a bound is requested.
 *
 * @tparam Value_type value type of the bounds
 *
 * TODO: requirements for Value_type?
 */
template <typename Value_type> class Bounds {
public:
    using Implied_value_type = Implied_value<Value_type>;
    using Constraint_type = Linear_constraint<Value_type>;
    using Models_type = Theory_models<Value_type>;

    /** Get current tightest implied upper bound
     *
     * @param models partial assignment of variables
     * @return tightest upper bound or maximal value if there is no implied upper bound
     */
    inline Implied_value_type upper_bound(Models_type const& models)
    {
        remove_obsolete(ub, models);

        if (ub.empty()) // no bound
        {
            return {std::numeric_limits<Value_type>::max(), Constraint_type{}};
        }
        else // there is at least one implied upper bound
        {
            return ub.back();
        }
    }

    /** Get current tightest implied lower bound
     *
     * @param models partial assignment of variables
     * @return tightest lower bound or minimal value if there is no implied lower bound
     */
    inline Implied_value_type lower_bound(Models_type const& models)
    {
        remove_obsolete(lb, models);

        if (lb.empty()) // no bound
        {
            return {std::numeric_limits<Value_type>::lowest(), Constraint_type{}};
        }
        else // there is at least one implied lower bound
        {
            return lb.back();
        }
    }

    /** Check whether there is an inequality of type `x != value`
     * 
     * @param models partial assignment of variables
     * @param value checked value
     * @return implied inequality or none, if there is none.
     */
    std::optional<Implied_value_type> inequality(Models_type const& models, Value_type value)
    {
        // remove obsolete values
        disallowed.erase(std::remove_if(disallowed.begin(), disallowed.end(),
                                        [&](auto v) { return is_obsolete(models, v.reason()); }),
                         disallowed.end());

        // check if value is in the list
        auto it = std::find_if(disallowed.begin(), disallowed.end(),
                               [value](auto v) { return v.value() == value; });
        if (it == disallowed.end())
        {
            return {};
        }
        return *it;
    }

    /** Add a new value to the list of disallowed values
     *
     * @param value value that cannot be assigned to the variable
     */
    inline void add_inequality(Implied_value_type value)
    {
        assert(value.reason().pred() == Order_predicate::EQ && value.reason().lit().is_negation());
        disallowed.push_back(value);
    }

    /** Add a new upper @p bound
     *
     * @param models partial assignment variables
     * @param bound new upper bound
     */
    inline void add_upper_bound(Models_type const& models, Implied_value_type bound)
    {
        auto current_bound = upper_bound(models);
        if (current_bound.value() > bound.value() ||
            (current_bound.value() == bound.value() && bound.reason().is_strict()))
        {
            ub.push_back(bound);
        }
    }

    /** Add a new lower @p bound
     *
     * @param models partial assignment of variables
     * @param bound new lower bound
     */
    inline void add_lower_bound(Models_type const& models, Implied_value_type bound)
    {
        auto current_bound = lower_bound(models);
        if (current_bound.value() < bound.value() ||
            (current_bound.value() == bound.value() && bound.reason().is_strict()))
        {
            lb.push_back(bound);
        }
    }

    /** Check whether @p value satisfies currently implied lower bound
     * 
     * @param models partial assignment of variables
     * @param value checked value
     * @return true if @p value is > `lower_bound()` and the bound is strict
     * @return true if @p value is >= `lower_bound()` and the bound is not strict
     */
    inline bool check_lower_bound(Models_type const& models, Value_type value)
    {
        auto lb = lower_bound(models);
        return lb.value() < value || (lb.value() == value && !lb.reason().is_strict());
    }

    /** Check whether @p value satisfies currently implied uppper bound
     * 
     * @param models partial assignment of variables
     * @param value checked value
     * @return true if @p value is < `upper_bound()` and the bound is strict
     * @return true if @p value is <= `upper_bound()` and the bound is not strict
     */
    inline bool check_upper_bound(Models_type const& models, Value_type value)
    {
        auto ub = upper_bound(models);
        return value < ub.value() || (ub.value() == value && !ub.reason().is_strict());
    }

    /** Check whether @p value is between currently implied lower and upper bound and there is no inequality that would disallow @p value
     * 
     * @param models partial assignment of variables
     * @param value checked value
     * @return true iff @p value is between `lower_bound()` and `upper_bound()` and there is no inequality that would prohibit @p value
     */
    inline bool is_allowed(Models_type const& models, Value_type value)
    {
        return !inequality(models, value) && check_lower_bound(models, value) && check_upper_bound(models, value);
    }

private:
    // stack with upper bounds
    std::vector<Implied_value_type> ub;
    // stack with lower bounds
    std::vector<Implied_value_type> lb;
    // list of values it should not be assigned to
    std::vector<Implied_value_type> disallowed;

    /** Remove obsolete bounds from the top of the @p bounds stack
     *
     * @param bounds stack with bounds
     * @param models partial assignment of variables
     */
    inline void remove_obsolete(std::vector<Implied_value_type>& bounds, Models_type const& models)
    {
        while (!bounds.empty() && is_obsolete(models, bounds.back().reason()))
        {
            bounds.pop_back();
        }
    }

    /** Check whether @p cons is obsolete given @p models
     *
     * @param models partial assignment of variables
     * @param cons checked constraint
     * @return true iff both watched variables (the first two variables) in @p cons are unassigned
     */
    inline bool is_obsolete(Models_type const& models, Constraint_type const& cons) const
    {
        // check that the constraint is still on the trail as a boolean variable
        if (cons.empty() || perun::eval(models.boolean(), cons.lit()) != true)
        {
            return true;
        }

        // check that the constraint is still unit
        auto [var_it, var_end] = cons.vars();
        assert(var_it != var_end);
        auto next_var_it = var_it + 1;
        if (next_var_it == var_end)
        {
            assert(!models.owned().is_defined(*var_it));
            return false;
        }

        return !models.owned().is_defined(*var_it) && !models.owned().is_defined(*next_var_it);
    }
};

} // namespace perun

#endif // PERUN_BOUNDS_H