#ifndef PERUN_BOUNDS_H
#define PERUN_BOUNDS_H

#include <algorithm>
#include <cassert>
#include <limits>
#include <optional>
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

    /** Create new implied value
     * 
     * @param val computed value implied by @p cons for the only unassigned variable in @p cons
     * @param cons unit constraint in @p models
     * @param models partial assignment of variables
     * @param level decision level at which @p val is implied
     */
    inline Implied_value(Value val, Constraint cons, Models const& models, int level)
        : val(val), cons(cons),
          timestamp(cons.size() >= 2 ? models.owned().timestamp(*++cons.vars().begin()) : -1),
          dec_level(level)
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
    inline Constraint reason() const { return cons; }

    /** Get decision level when this bound was added.
     * 
     * @return decision level of this bound
     */
    inline int level() const { return dec_level; }

    /** Check whether this value is obsolete.
     *
     * Value becomes obsolete if `reason()` is no longer on the trail, it is no longer a unit
     * constraint, or variables in `reason()` are assigned to different values than when this
     * object was created.
     *
     * @param models partial assignment of variables
     * @return true iff `value()` is no longer a valid implied value from `reason()`
     */
    inline bool is_obsolete(Models const& models) const
    {
        if (reason().empty() || perun::eval(models.boolean(), reason().lit()) != true)
        {
            return true; // reason() is no longer on the trail
        }

        // find the assigned watched variable
        auto [var_it, var_end] = cons.vars();
        assert(var_it != var_end);
        assert(!models.owned().is_defined(*var_it) ||
               std::all_of(cons.vars().begin(), cons.vars().end(),
                           [&](auto var_ord) { return models.owned().is_defined(var_ord); }));

        if (models.owned().is_defined(*var_it))
        {
            return false;
        }
        else // the first variable is unassigned
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
    Constraint cons;
    // timestamp of the most recently assigned variable in cons
    int timestamp;
    // decision level of this bound
    int dec_level;
};

/** This class keeps track of implied bounds and inequalities for a variable.
 *
 * Obsolete bounds are removed lazily when a bound is requested.
 *
 * @tparam Value value type of the bounds
 */
template <typename Value> class Bounds {
public:
    using Implied_value_type = Implied_value<Value>;
    using Constraint = Linear_constraint<Value>;
    using Models = Theory_models<Value>;

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
    Implied_value_type const* inequality(Models const& models, Value value)
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
            return nullptr;
        }
        return &*it;
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
    inline void add_upper_bound(Models const& models, Implied_value_type&& bound)
    {
        remove_obsolete(ub, models);
        insert(ub, std::move(bound), [this](auto bnd, auto other_bnd) { 
            return less(bnd, other_bnd); 
        });
    }

    /** Add a new lower @p bound
     *
     * @param models partial assignment of variables
     * @param bound new lower bound
     */
    inline void add_lower_bound(Models const& models, Implied_value_type&& bound)
    {
        remove_obsolete(lb, models);
        insert(lb, std::move(bound), [this](auto bnd, auto other_bnd) { 
            return greater(bnd, other_bnd); 
        });
    }

    /** Check whether @p value satisfies currently implied lower bound
     *
     * @param models partial assignment of variables
     * @param value checked value
     * @return true if @p value is > `lower_bound()` and the bound is strict
     * @return true if @p value is >= `lower_bound()` and the bound is not strict
     */
    inline bool check_lower_bound(Models const& models, Value value)
    {
        if (auto lb = lower_bound(models))
        {
            return lb->value() < value || (lb->value() == value && !lb->reason().is_strict());
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
    inline bool check_upper_bound(Models const& models, Value value)
    {
        if (auto ub = upper_bound(models))
        {
            return value < ub->value() || (ub->value() == value && !ub->reason().is_strict());
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
    inline bool is_allowed(Models const& models, Value value)
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

    /** Check whether @p lhs is strictly less than @p rhs
     *
     * @param lhs first value
     * @param rhs second value
     * @return true iff @p lhs < @p rhs
     */
    inline bool less(Implied_value_type const& lhs, Implied_value_type const& rhs) const
    {
        return lhs.value() < rhs.value() || (lhs.value() == rhs.value() &&
                                             lhs.reason().is_strict() && !rhs.reason().is_strict());
    }

    /** Check whether @p lhs is strictly greater than @p rhs
     *
     * @param lhs first value
     * @param rhs second value
     * @return true iff @p lhs > @p rhs
     */
    inline bool greater(Implied_value_type const& lhs, Implied_value_type const& rhs) const
    {
        return lhs.value() > rhs.value() || (lhs.value() == rhs.value() &&
                                             lhs.reason().is_strict() && !rhs.reason().is_strict());
    }

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

    /** Insert @p bound to @p bounds if it @p is_better than the best bound at the decision level 
     * of @p bound 
     *
     * @param bounds list of bounds sorted by decision level
     * @param bound new bound to insert to @p bounds
     * @param is_better predicate which, given two implied values, returns true iff the first 
     * value is strictly better than the second value
     */
    template<typename Predicate>
    inline void insert(std::vector<Implied_value_type>& bounds, Implied_value_type&& bound, Predicate&& is_better)
    {
        assert(std::is_sorted(bounds.begin(), bounds.end(), [](auto&& lhs, auto&& rhs) {
            return lhs.level() < rhs.level();
        }));

        // find position of the new element
        auto rev_it = std::find_if(bounds.rbegin(), bounds.rend(), [&](auto&& other_bnd) {
            return other_bnd.level() <= bound.level();
        });

        // insert the new bound if it is better
        if (rev_it == bounds.rend() || is_better(bound, *rev_it))
        {
            auto it = ++bounds.insert(rev_it.base(), std::move(bound));
            bounds.erase(it, std::find_if(it, bounds.end(), [&](auto&& other_bnd) {
                return is_better(other_bnd, bound);
            }));
        }

    }
};

} // namespace perun

#endif // PERUN_BOUNDS_H