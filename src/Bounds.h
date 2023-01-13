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
template <typename Value>
class Theory_models {
public:
    Theory_models(Model<bool>* bool_model, Model<Value>* owned_model) : bool_model(bool_model), owned_model(owned_model) {}

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

    /** Get current tightest implied upper bound
     *
     * @param model current partial assignment of LRA variables
     * @return tightest upper bound or maximal value if there is no implied upper bound
     */
    inline Implied_value_type upper_bound(Model<Value_type> const& model)
    {
        remove_obsolete(ub, model);

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
     * @param model current partial assignment of LRA variables
     * @return tightest lower bound or minimal value if there is no implied lower bound
     */
    inline Implied_value_type lower_bound(Model<Value_type> const& model)
    {
        remove_obsolete(lb, model);

        if (lb.empty()) // no bound
        {
            return {std::numeric_limits<Value_type>::lowest(), Constraint_type{}};
        }
        else // there is at least one implied lower bound
        {
            return lb.back();
        }
    }

    /** Check whether there is an inequality that would disallow @p value
     *
     * @param model current partial assignment of LRA variables
     * @param value checked value
     * @return true iff there is no linear constraint that would disallow @p value
     */
    inline bool is_allowed(Model<Value_type> const& model, Value_type value)
    {
        // remove obsolete values
        disallowed.erase(std::remove_if(disallowed.begin(), disallowed.end(),
                                        [&](auto v) { return is_obsolete(model, v.reason()); }),
                         disallowed.end());

        // check if value is in the list
        return std::find_if(disallowed.begin(), disallowed.end(),
                            [value](auto v) { return v.value() == value; }) == disallowed.end();
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
     * @param model current partial assignment of LRA variables
     * @param bound new upper bound
     */
    inline void add_upper_bound(Model<Value_type> const& model, Implied_value_type bound)
    {
        auto current_bound = upper_bound(model);
        if (current_bound.value() > bound.value() ||
            (current_bound.value() == bound.value() && bound.reason().is_strict()))
        {
            ub.push_back(bound);
        }
    }

    /** Add a new lower @p bound
     *
     * @param model current partial assignment of LRA variables
     * @param bound new lower bound
     */
    inline void add_lower_bound(Model<Value_type> const& model, Implied_value_type bound)
    {
        auto current_bound = lower_bound(model);
        if (current_bound.value() < bound.value() ||
            (current_bound.value() == bound.value() && bound.reason().is_strict()))
        {
            lb.push_back(bound);
        }
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
     * @param model current partial assignment of LRA variables
     */
    inline void remove_obsolete(std::vector<Implied_value_type>& bounds,
                                Model<Value_type> const& model)
    {
        while (!bounds.empty() && is_obsolete(model, bounds.back().reason()))
        {
            bounds.pop_back();
        }
    }

    /** Check whether @p cons is obsolete given @p model
     *
     * @param model current partial assignment of LRA variables
     * @param cons checked constraint
     * @return true iff both watched variables (the first two variables) in @p cons are unassigned
     */
    inline bool is_obsolete(Model<Value_type> const& model, Constraint_type const& cons) const
    {
        auto [var_it, var_end] = cons.vars();
        assert(var_it != var_end);
        auto next_var_it = var_it + 1;
        if (next_var_it == var_end)
        {
            assert(!model.is_defined(*var_it));
            return false;
        }

        return !model.is_defined(*var_it) && !model.is_defined(*next_var_it);
    }

    /** Check that the first variable in @p reason is the only unassigned variable in @p model
     *
     * @param model current partial assignment of LRA variables
     * @param reason checked linear constraint
     * @return true iff @p reason is non-empty and the first variable is the only unassigned
     * variable
     */
    inline bool is_unit(Model<Value_type> const& model, Constraint_type const& reason) const
    {
        return !reason.empty() && !model.is_defined(reason.vars().front()) &&
               std::all_of(++reason.vars().begin(), reason.vars().end(),
                           [&model](auto v) { return model.is_defined(v); });
    }

    /** Check if @p reason is a unit constraint that implies an upper bound
     *
     * @param model current partial assignment of LRA variables
     * @param reason linear constraint
     * @return true iff @p reason is a unit constraint that implies an upper bound
     */
    inline bool is_upper_bound(Model<Value_type> const& model, Constraint_type const& reason) const
    {
        if (!is_unit(model, reason))
        {
            return false;
        }
        return (reason.coef().front() > 0 && !reason.lit().is_negation() &&
                reason.pred() != Order_predicate::EQ) ||
               (reason.coef().front() < 0 && reason.lit().is_negation() &&
                reason.pred() != Order_predicate::EQ);
    }

    /** Check if @p reason is a unit constraint that implies a lower bound
     *
     * @param model current partial assignment of LRA variables
     * @param reason linear constraint
     * @return true iff @p reason is a unit constraint that implies a lower bound
     */
    inline bool is_lower_bound(Model<Value_type> const& model, Constraint_type const& reason) const
    {
        if (!is_unit(model, reason))
        {
            return false;
        }
        return (reason.coef().front() > 0 && reason.lit().is_negation() &&
                reason.pred() != Order_predicate::EQ) ||
               (reason.coef().front() < 0 && !reason.lit().is_negation() &&
                reason.pred() != Order_predicate::EQ);
    }
};

} // namespace perun

#endif // PERUN_BOUNDS_H