#ifndef YAGA_VARIABLE_BOUNDS_H
#define YAGA_VARIABLE_BOUNDS_H

#include <algorithm>
#include <cassert>
#include <concepts>
#include <functional>
#include <limits>
#include <optional>
#include <type_traits>
#include <vector>

#include "Linear_constraints.h"
#include "Model.h"

namespace yaga {

/** Reference to models relevant for a theory
 *
 * @tparam Value type of variables of the theory
 */
template <typename Value> class Theory_models {
public:
    Theory_models(Model<bool>& bool_model, Model<Value>& owned_model)
        : bool_model(bool_model), owned_model(owned_model)
    {
    }

    inline Theory_models(Theory_models const&) = delete;
    inline Theory_models& operator=(Theory_models const&) = delete;

    /** Get model of boolean variables
     *
     * @return partial assignment of boolean variables
     */
    inline Model<bool> const& boolean() const { return bool_model; }

    /** Get model of boolean variables
     *
     * @return partial assignment of boolean variables
     */
    inline Model<bool>& boolean() { return bool_model; }

    /** Get model of variables owned by the theory
     *
     * @return partial assignment of variables owned by the theory
     */
    inline Model<Value> const& owned() const { return owned_model; }

    /** Get model of variables owned by the theory
     *
     * @return partial assignment of variables owned by the theory
     */
    inline Model<Value>& owned() { return owned_model; }

private:
    Model<bool>& bool_model;
    Model<Value>& owned_model;
};

/** Value implied by a linear constraint
 *
 * @tparam Value
 */
template <typename Value> class Implied_value {
public:
    using Constraint = Linear_constraint<Value>;
    using Models = Theory_models<Value>;

    /** Create new value implied by a unit linear constraint
     *
     * @param var bounded variable
     * @param val computed value implied by @p cons for the only unassigned variable in @p cons
     * @param cons unit constraint in @p models
     * @param models partial assignment of variables
     */
    Implied_value(int var, Value const& val, Constraint const& cons, Models const& models)
        : bound_var(var), val(val), cons(cons)
    {
        assert(!cons.empty());
        assert(!models.owned().is_defined(cons.vars().front()));
        assert(std::all_of(cons.vars().begin() + 1, cons.vars().end(),
                           [&](auto var) { return models.owned().is_defined(var); }));
        compute_timestamps(models);
    }

    /** Create a bound deduced from other bounds
     *
     * @tparam Bound_range range with bounds
     * @param var bounded variable
     * @param val computed value implied by @p cons for @p var given @p deps
     * @param cons linear constraint where all variables are either assigned or bounded by @p deps
     * @param models partial assignment of variables
     * @param level decision level at which @p val is implied
     * @param deps other bounds this bound depends on
     */
    template <std::ranges::range Bound_range>
    Implied_value(int var, Value const& val, Constraint const& cons, Models const& models, Bound_range&& deps)
        : bound_var(var), val(val), cons(cons), deps(deps.begin(), deps.end())
    {
        assert(!cons.empty());
        compute_timestamps(models);
    }

    /** Get the implied value
     *
     * @return implied value
     */
    inline Value const& value() const { return val; }

    /** Get linear constraint that implied this bound.
     *
     * @return linear constraint that implied this bound
     */
    inline Constraint const& reason() const { return cons; }

    /** Get variable for which this bound holds
     *
     * @return theory variable bounded by this bound
     */
    inline int var() const { return bound_var; }

    /** Other bounds on which this bound depends
     *
     * @return range of bounds necessary for this bound
     */
    inline auto const& bounds() const { return deps; }

    /** Check if this bound is strict (<, >)
     *
     * @return true iff this bound is strict (<, >)
     */
    inline bool is_strict() const
    {
        return reason().is_strict() ||
               std::any_of(deps.begin(), deps.end(), [](auto const& other_bound) {
                   return other_bound.reason().is_strict();
               });
    }

    /** Check whether this value is obsolete.
     *
     * Value becomes obsolete if `reason()` is no longer on the trail, any dependency in `bounds()`
     * is obsolete, or variables in `reason()` are assigned to different values than when this
     * object was created.
     *
     * @param models partial assignment of variables
     * @return true iff `value()` is no longer a valid implied value from `reason()`
     */
    inline bool is_obsolete(Models const& models) const
    {
        // if reason() is assigned to a different value or it is not on the trail
        if (eval(models.boolean(), reason().lit()) != true ||
            models.boolean().timestamp(reason().lit().var().ord()) > cons_time)
        {
            return true;
        }

        // obsolete if variables assigned at the time when we computed the bound are unassigned or
        // assigned to a different value
        for (auto var : reason().vars())
        {
            if (var != bound_var)
            {
                // if var is supposed to be assigned
                auto it = std::find_if(deps.begin(), deps.end(),
                                       [var](auto const& bnd) { return bnd.bound_var == var; });
                if (it == deps.end() &&
                    (!models.owned().is_defined(var) || models.owned().timestamp(var) > var_time))
                {
                    return true;
                }
            }
        }

        // obsolete if any bound, on which this bound depends, is obsolete
        for (auto const& bnd : deps)
        {
            if (bnd.is_obsolete(models))
            {
                return true;
            }
        }

        return false;
    }

private:
    // bounded theory variable ordinal number
    int bound_var;
    // implied bound
    Value val;
    // linear constraint that implied the bound
    Constraint cons;
    // bounds used to derive this bound
    std::vector<Implied_value<Value>> deps;
    // timestamp of the boolean variable of constraint
    int cons_time = 0;
    // max timestamp of assigned theory variables on which this bound depends
    int var_time = 0;

    /** Compute maximal timestamp of a boolean/theory variable used for this bound
     *
     * @param models partial assignment of variables
     */
    inline void compute_timestamps(Models const& models)
    {
        cons_time = models.boolean().timestamp(reason().lit().var().ord());
        var_time = 0;
        for (auto var : reason().vars())
        {
            if (var != bound_var && models.owned().is_defined(var))
            {
                var_time = std::max<int>(var_time, models.owned().timestamp(var));
            }
        }
    }
};

/** Compare computed bounds.
 *
 * @tparam Value value type of theory variables (e.g., a fraction for LRA)
 * @tparam Less operator which compares two `Value` types and returns true iff the first value is
 * strictly better than the second value.
 */
template <typename Value, std::predicate<Value, Value> Less> struct Bound_comparer {
    using Models = Theory_models<Value>;
    using Implied_value_type = Implied_value<Value>;

    /** Check whether @p lhs is a strictly better bound than @p rhs
     *
     * @param models partial assignment of variables
     * @param lhs first bound
     * @param rhs second bound
     * @return true iff @p lhs is strictly better than @p rhs
     */
    bool operator()(Implied_value_type const& lhs, Implied_value_type const& rhs) const
    {
        // if lhs is strictly better than rhs
        if (Less{}(lhs.value(), rhs.value()))
        {
            return true;
        }

        // if the bound values are the same
        if (lhs.value() == rhs.value())
        {
            auto lhs_strict = lhs.is_strict();
            auto rhs_strict = rhs.is_strict();
            if (lhs_strict && !rhs_strict)
            {
                return true;
            }
            else if (lhs_strict == rhs_strict)
            {
                return false;
            }
        }
        return false;
    }
};

/** This class keeps track of implied bounds and inequalities for a single variable.
 *
 * Obsolete bounds are removed lazily when a bound is requested.
 *
 * @tparam Value value type of the bounds
 */
template <typename Value> class Variable_bounds {
public:
    using Implied_value_type = Implied_value<Value>;
    using Constraint = Linear_constraint<Value>;
    using Models = Theory_models<Value>;
    using Lower_bound_comparer = Bound_comparer<Value, std::greater<Value>>;
    using Upper_bound_comparer = Bound_comparer<Value, std::less<Value>>;

    /** Get current tightest implied upper bound
     *
     * @param models partial assignment of variables
     * @return tightest upper bound or none if there is no implied upper bound
     */
    inline Implied_value_type const* upper_bound(Models const& models)
    {
        remove_obsolete(ub, models);

        if (ub.empty()) // no bound
        {
            return nullptr;
        }
        else // there is at least one implied upper bound
        {
            return &ub.back();
        }
    }

    /** Get current tightest implied lower bound
     *
     * @param models partial assignment of variables
     * @return tightest lower bound or none if there is no implied lower bound
     */
    inline Implied_value_type const* lower_bound(Models const& models)
    {
        remove_obsolete(lb, models);

        if (lb.empty()) // no bound
        {
            return nullptr;
        }
        else // there is at least one implied lower bound
        {
            return &lb.back();
        }
    }

    /** Check whether there is an inequality of type `x != value`
     *
     * @param models partial assignment of variables
     * @param value checked value
     * @return implied inequality or none, if there is none.
     */
    Implied_value_type const* inequality(Models const& models, Value const& value)
    {
        // remove obsolete values
        remove_all_obsolete(disallowed, models);

        // check if value is in the list
        auto it = std::find_if(disallowed.begin(), disallowed.end(),
                               [&](auto const& other) { return other.value() == value; });
        if (it == disallowed.end())
        {
            return nullptr;
        }
        return &*it;
    }

    /** Add a new value to the list of disallowed values
     *
     * @param models partial assignment of variables
     * @param value value that cannot be assigned to the variable
     * @returns true iff @p value has been added to the list of disallowed values
     */
    inline bool add_inequality(Models const& models, Implied_value_type&& value)
    {
        assert(value.reason().pred() == Order_predicate::eq && value.reason().lit().is_negation());

        auto neq = inequality(models, value.value());
        if (!neq || neq->reason().lit() != value.reason().lit())
        {
            disallowed.push_back(value);
            return true;
        }
        return false;
    }

    /** Add a new upper @p new_bound
     *
     * @param models partial assignment variables
     * @param new_bound new upper bound
     * @returns true iff @p new_bound is better than current bound
     */
    inline bool add_upper_bound(Models const& models, Implied_value_type&& new_bound)
    {
        Upper_bound_comparer is_better;
        auto bound = upper_bound(models);
        if (!bound || is_better(new_bound, *bound))
        {
            ub.push_back(std::move(new_bound));
            return true;
        }
        return false;
    }

    /** Add a new lower @p new_bound
     *
     * @param models partial assignment of variables
     * @param new_bound new lower bound
     * @returns true iff @p new_bound is better than current bound
     */
    inline bool add_lower_bound(Models const& models, Implied_value_type&& new_bound)
    {
        Lower_bound_comparer is_better;
        auto bound = lower_bound(models);
        if (!bound || is_better(new_bound, *bound))
        {
            lb.push_back(std::move(new_bound));
            return true;
        }
        return false;
    }

    /** Check whether @p value satisfies currently implied lower bound
     *
     * @param models partial assignment of variables
     * @param value checked value
     * @return true if @p value is > `lower_bound()` and the bound is strict
     * @return true if @p value is >= `lower_bound()` and the bound is not strict
     */
    inline bool check_lower_bound(Models const& models, Value const& value)
    {
        if (auto lb = lower_bound(models))
        {
            return lb->value() < value || (lb->value() == value && !lb->is_strict());
        }
        return true;
    }

    /** Check whether @p value satisfies currently implied upper bound
     *
     * @param models partial assignment of variables
     * @param value checked value
     * @return true if @p value is < `upper_bound()` and the bound is strict
     * @return true if @p value is <= `upper_bound()` and the bound is not strict
     */
    inline bool check_upper_bound(Models const& models, Value const& value)
    {
        if (auto ub = upper_bound(models))
        {
            return value < ub->value() || (ub->value() == value && !ub->is_strict());
        }
        return true;
    }

    /** Check whether @p value is between currently implied lower and upper bound and there is no
     * inequality that would disallow @p value
     *
     * @param models partial assignment of variables
     * @param value checked value
     * @return true iff @p value is between `lower_bound()` and `upper_bound()` and there is no
     * inequality that would prohibit @p value
     */
    inline bool is_allowed(Models const& models, Value const& value)
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
    inline void remove_obsolete(std::vector<Implied_value_type>& bounds, Models const& models)
    {
        while (!bounds.empty() && bounds.back().is_obsolete(models))
        {
            bounds.pop_back();
        }
    }

    /** Remove all obsolete implied values from the list @p values
     *
     * @param values list of implied values
     * @param models partial assignment of variables
     */
    inline void remove_all_obsolete(std::vector<Implied_value_type>& values, Models const& models)
    {
        values.erase(std::remove_if(values.begin(), values.end(),
                                    [&](auto const& other) { return other.is_obsolete(models); }),
                     values.end());
    }
};

} // namespace yaga

#endif // YAGA_VARIABLE_BOUNDS_H