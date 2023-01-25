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

/** Value implied by a linear constraint
 *
 * @tparam Value_type
 */
template <typename Value> class Implied_value {
public:
    using Constraint_type = Linear_constraint<Value>;
    using Models_type = Theory_models<Value>;

    inline Implied_value(Value val) : val(val), timestamp(-1) {}

    inline Implied_value(Value val, Constraint_type cons, Models_type const& models)
        : val(val), cons(cons),
          timestamp(cons.size() >= 2 ? models.owned().timestamp(*++cons.vars().begin()) : -1)
    {
    }

    /** Get the implied value
     *
     * @return implied value
     */
    inline Value value() const { return val; }

    /** Get linear constraint that implied this bound.
     *
     * @return linear constraint that implied this bound
     */
    inline Constraint_type reason() const { return cons; }

    /** Check whether this value is obsolete.
     *
     * Value becomes obsolete if `reason()` is no longer on the trail, it is no longer a unit
     * constraint, or variables in `reason()` are assigned to different values than when this
     * object was created.
     *
     * @param models partial assignment of variables
     * @return true iff `value()` is no longer a valid implied value from `reason()`
     */
    inline bool is_obsolete(Models_type const& models) const
    {
        if (reason().empty() || perun::eval(models.boolean(), reason().lit()) != true)
        {
            return true; // reason() is no longer on the trail
        }

        // find the assigned watched variable
        auto [var_it, var_end] = cons.vars();
        assert(var_it != var_end);
        if (!models.owned().is_defined(*var_it))
        {
            ++var_it;
        }

        return var_it != var_end && (!models.owned().is_defined(*var_it) ||
               models.owned().timestamp(*var_it) != timestamp);
    }

private:
    // implied bound
    Value val;
    // linear constraint that implied the bound
    Constraint_type cons;
    // timestamp of the most recently assigned variable in cons
    int timestamp;
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
            return {std::numeric_limits<Value_type>::max()};
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
            return {std::numeric_limits<Value_type>::lowest()};
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
                                        [&](auto v) { return v.is_obsolete(models); }),
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
        assert(value.reason().pred() == Order_predicate::eq && value.reason().lit().is_negation());
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

    /** Check whether @p value is between currently implied lower and upper bound and there is no
     * inequality that would disallow @p value
     *
     * @param models partial assignment of variables
     * @param value checked value
     * @return true iff @p value is between `lower_bound()` and `upper_bound()` and there is no
     * inequality that would prohibit @p value
     */
    inline bool is_allowed(Models_type const& models, Value_type value)
    {
        return !inequality(models, value) && check_lower_bound(models, value) &&
               check_upper_bound(models, value);
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
        while (!bounds.empty() && bounds.back().is_obsolete(models))
        {
            bounds.pop_back();
        }
    }
};

} // namespace perun

#endif // PERUN_BOUNDS_H