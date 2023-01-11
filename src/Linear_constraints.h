#ifndef PREUN_LINEAR_CONSTRAINTS_H
#define PREUN_LINEAR_CONSTRAINTS_H

#include <algorithm>
#include <cassert>
#include <concepts>
#include <functional>
#include <iterator>
#include <ranges>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "Literal.h"
#include "Model.h"
#include "Variable.h"

namespace perun {

/** Predicate of the type `x < y`, `x <= y`, or `x = y`.
 */
class Order_predicate {
public:
    enum Type {
        EQ,  // =
        LT,  // <
        LEQ, // <=
    };

    inline Order_predicate(Type type) : type(type) {}

    /** Conversion to enum type
     *
     * @return enum type
     */
    inline operator Type() const { return type; }

    /** Compare two order predicates
     *
     * @param other other predicate
     * @return true iff this predicate is equivalent to @p other
     */
    inline bool operator==(Order_predicate const& other) const { return type == other.type; }

    /** Compare two order predicates
     *
     * @param other other predicate
     * @return true iff this predicate is not equivalent to @p other
     */
    inline bool operator!=(Order_predicate const& other) const { return !operator==(other); }

    /** Compare predicate with enum type
     *
     * @param other_type other predicate type
     * @return true iff type of this predicate is equivalent to @p other_type
     */
    inline bool operator==(Type other_type) const { return type == other_type; }

    /** Compare predicate with enum type
     *
     * @param other_type other predicate type
     * @return true iff type of this predicate is not equivalent to @p other_type
     */
    inline bool operator!=(Type other_type) const { return !operator==(other_type); }

    /** Evaluate the predicate on a totally ordered type.
     *
     * @tparam T totally ordered type
     * @param lhs left-hand-side of the predicate
     * @param rhs right-hand-side of the predicate
     * @return true iff the predicate is true for (lhs, rhs)
     */
    template <std::totally_ordered T> inline bool operator()(T const& lhs, T const& rhs) const
    {
        switch (type)
        {
        case EQ:
            return lhs == rhs;
        case LT:
            return lhs < rhs;
        case LEQ:
            return lhs <= rhs;
        }
        assert(false);
        return false;
    }

private:
    Type type;
};

template <typename Value> class Linear_constraints;

/** Represents a linear constraint of the type `<x, c> @ b` where:
 * -# `x` is a vector of variables
 * -# `c` is a corresponding vector of coefficients
 * -# `<x, c>` is a dot product
 * -# `@` is one of <, <=, =
 * -# `b` is a constant
 */
template <typename Value> class Linear_constraint {
public:
    friend class Linear_constraints<Value>;

    using Value_type = Value;
    using Range_type = std::pair<int, int>;

    /** Create an empty linear constraint
     */
    inline Linear_constraint() : position({0, 0}), predicate(Order_predicate::EQ), constant(0) {}

    /** Create a new linear constraint
     *
     * @param lit literal that represents this constraint
     * @param position index range of values of this constraint in Linear_constraints
     * @param pred predicate of the constraint
     * @param rhs constant value on the right-hand-side of the constraint
     */
    inline Linear_constraint(Literal lit, Range_type position, Order_predicate pred, Value_type rhs,
                             Linear_constraints<Value_type>* constraints)
        : position(position), predicate(pred), literal(lit), constant(rhs), constraints(constraints)
    {
    }

    /** Get predicate of this constraint
     *
     * @return predicate of this constraint
     */
    inline Order_predicate pred() const { return predicate; }

    /** Get the constant value on the right-hand-side of this constraint
     *
     * @return value on the right-hand-side of this constraint
     */
    inline Value_type rhs() const { return constant; }

    /** Get literal that represents this constraint
     *
     * @return literal that is equal to this constraint
     */
    inline Literal lit() const { return literal; }

    /** Check whether there are some variables with a non-zero coefficient in this constraint
     *
     * @return true iff this constraint does not have any variables
     */
    inline bool empty() const { return pos().first >= pos().second; }

    /** Get number of variables in this constraint
     *
     * @return number of variables in this constraint
     */
    inline int size() const { return position.second - position.first; }

    /** Get range of variables of this constraint
     *
     * @return range of variables of this constraint
     */
    inline auto vars() const { return constraints->vars(*this); }

    /** Get range of coefficients of this constraint
     *
     * @return range of coefficients of this constraint
     */
    inline auto coef() const { return constraints->coef(*this); }

    /** Create a linear constraint that represents a negation of this constraint
     *
     * @return new linear constraint that represents negation of this constraint
     */
    inline Linear_constraint negate() const
    {
        return {lit().negate(), pos(), pred(), rhs(), constraints};
    }

    /** Check if this linear constraint represents a strict inequality (< or >)
     *
     * @return true iff pred() is < and lit() is not negated, or pred() is <= and lit() is negated
     */
    inline bool is_strict() const
    {
        return (lit().is_negation() && pred() == Order_predicate::LEQ) ||
               (!lit().is_negation() && pred() == Order_predicate::LT);
    }

    /** Evaluate this constraint in @p model
     *
     * @param model current partial assignment of variables
     * @return true iff this constraint is true in @p model
     */
    inline bool eval(Model<Value_type> const& model) const
    {
        return constraints->eval(model, *this);
    }

    /** Evaluate this constraint except for the first unassigned variable and return the computed
     * constant on the right-hand-side of the constraint.
     *
     * For example: `2 * x + 3 * y <= 10` with `y = 2` will return `4` since `2 * x <= 4` if `y =
     * 2`.
     *
     * Precondition: all variables, except the first one, are assigned in @p model
     *
     * @param model current partial assignment of variables
     * @return new constant value on the right-hand-side of the constraint after evaluation
     */
    inline Value_type implied_value(Model<Value_type> const& model) const
    {
        return constraints->implied_value(model, *this);
    }

private:
    // index range of values in constraints
    Range_type position;
    // predicate of the constraint
    Order_predicate predicate;
    // literal that that represents this constraint
    Literal literal;
    // right-hand-side of the constraint
    Value_type constant;
    // container which contains this constraint
    Linear_constraints<Value_type>* constraints;

    /** Get location of values of this constraint in Linear_constraints
     *
     * @return range of indices
     */
    inline Range_type pos() const { return position; }
};

/** Evaluate linear constraint in @p model
 * 
 * @tparam Value_type type of constants in @p cons
 * @param model partial assignment of LRA variables
 * @param cons linear constraint to evaluate
 * @return true if @p cons is true in model, false if @p cons is false in model. None, if @p cons is undefined.
 */
template<typename Value_type>
inline std::optional<bool> eval(Model<Value_type> const& model, Linear_constraint<Value_type> const& cons)
{
    for (auto var : cons.vars())
    {
        if (!model.is_defined(var))
        {
            return {};
        }
    }
    return cons.eval(model);
}

/** Hash functor for Linear_constraint that disregards order of variables.
 *
 * @tparam Value_type value type of coefficients in the constraint
 */
template <typename Value_type> class Linear_constraint_hash {
public:
    /** Create a hash of a linear constraint @p cons that ignores order of variables
     *
     * @param cons linear constraint
     * @return hash of @p cons such that any permutation of variables in @p cons produces the same
     * hash
     */
    std::size_t operator()(Linear_constraint<Value_type> const& cons) const
    {
        std::size_t hash = coef_hash(cons.rhs());
        for (auto var : cons.vars())
        {
            hash ^= var_hash(var);
        }

        for (auto coef : cons.coef())
        {
            hash ^= coef_hash(coef);
        }
        return hash;
    }

private:
    std::hash<int> var_hash;
    std::hash<Value_type> coef_hash;
};

/** Equality compare functor for Linear_constraint that disregards order or variables.
 *
 * @tparam Value_type value type of coefficients in the constraint
 */
template <typename Value_type> class Linear_constraint_equal {
public:
    bool operator()(Linear_constraint<Value_type> const& lhs,
                    Linear_constraint<Value_type> const& rhs)
    {
        if (lhs.size() != rhs.size() || lhs.pred() != rhs.pred() || lhs.rhs() != rhs.rhs())
        {
            return false;
        }

        coef.clear();
        coef.resize(1 + *std::max_element(lhs.vars().begin(), lhs.vars().end()), Value_type{0});

        // map variables -> coefficients in `lhs`
        auto lhs_coef_it = lhs.coef().begin();
        for (auto var : lhs.vars())
        {
            assert(lhs_coef_it != lhs.coef().end());
            assert(var < static_cast<int>(coef.size()));
            coef[var] = *lhs_coef_it++;
        }

        // check that the coefficients are the same
        auto rhs_coef_it = rhs.coef().begin();
        for (auto var : rhs.vars())
        {
            assert(rhs_coef_it != rhs.coef().end());
            if (coef[var] != *rhs_coef_it)
            {
                return false;
            }
        }
        return true;
    }

    bool operator()(Linear_constraint<Value_type> const& lhs,
                    Linear_constraint<Value_type> const& rhs) const
    {
        if (lhs.size() != rhs.size() || lhs.pred() != rhs.pred() || lhs.rhs() != rhs.rhs())
        {
            return false;
        }

        auto lhs_coef_it = lhs.coef().begin();
        for (auto var : lhs.vars())
        {
            assert(lhs_coef_it != lhs.coef().end());
            auto rhs_var_it = std::find(rhs.vars().begin(), rhs.vars().end(), var);
            if (rhs_var_it == rhs.vars().end())
            {
                return false;
            }

            auto rhs_coef_it = rhs.coef().begin() + std::distance(rhs.vars().begin(), rhs_var_it);
            if (*lhs_coef_it != *rhs_coef_it)
            {
                return false;
            }

            ++lhs_coef_it;
        }
        return true;
    }

private:
    // map variable -> coefficient value (auxiliary memory for operator())
    std::vector<Value_type> coef;
};

/** Repository of linear constraints.
 *
 * Added constraints are normalized and deduplicated so that there is at most one boolean variable
 * that represents a given constraint or its negation.
 */
template <typename Value> class Linear_constraints {
public:
    using Value_type = Value;
    using Constraint_type = Linear_constraint<Value>;

    /** Create a new linear constraint.
     *
     * The constraint is normalized. The returned constraint might represent negation of the input
     * constraint in which case, literal of the returned constraint will be negated.
     *
     * @param var_range ordinal numbers of variables in the constraint
     * @param coef_range coefficients of variables in the constraint
     * @param pred predicate of the constraint
     * @param rhs constant on the right-hand-side of the constrant
     * @return new constraint together with literal that represents that constraint
     */
    template <std::ranges::range Var_range, std::ranges::range Value_range>
    Constraint_type make(Var_range&& var_range, Value_range&& coef_range, Order_predicate pred,
                         Value_type rhs)
    {
        auto mult = find_norm_constant(var_range, coef_range);
        auto [lit, range] = add(mult, var_range, coef_range);

        auto cons = constraints.emplace_back(lit, range, norm_pred(mult, pred), mult * rhs, this);
        auto [it, is_inserted] = cons_set.insert(cons);
        if (!is_inserted) // remove the new constraint if it is a duplicate
        {
            variables.erase(cons.vars().begin(), cons.vars().end());
            coefficients.erase(cons.coef().begin(), cons.coef().end());
            constraints.pop_back();
        }

        // negate literal if `*it` represents negation of the input constraint
        lit = it->lit();
        if (pred != Order_predicate::EQ && mult < Value_type{0})
        {
            lit = lit.negate();
        }

        return {lit, it->pos(), it->pred(), it->rhs(), this};
    }

    /** Get range of variables of @p cons
     *
     * @param cons linear constraint
     * @return range of variables of @p cons
     */
    inline auto vars(Constraint_type const& cons)
    {
        return std::ranges::subrange{variables.begin() + cons.pos().first,
                                     variables.begin() + cons.pos().second};
    }

    /** Get range of variables of @p cons
     *
     * @param cons linear constraint
     * @return range of variables of @p cons
     */
    inline auto vars(Constraint_type const& cons) const
    {
        return std::ranges::subrange{variables.begin() + cons.pos().first,
                                     variables.begin() + cons.pos().second};
    }

    /** Get range of coefficients of @p cons
     *
     * @param cons linear constraint
     * @return range of coefficients of @p cons
     */
    inline auto coef(Constraint_type const& cons)
    {
        return std::ranges::subrange{coefficients.begin() + cons.pos().first,
                                     coefficients.begin() + cons.pos().second};
    }

    /** Get range of coefficients of @p cons
     *
     * @param cons linear constraint
     * @return range of coefficients of @p cons
     */
    inline auto coef(Constraint_type const& cons) const
    {
        return std::ranges::subrange{coefficients.begin() + cons.pos().first,
                                     coefficients.begin() + cons.pos().second};
    }

    /** Evaluate linear constraint in @p model
     *
     * Precondition: all variables in the @p cons are assigned.
     *
     * @param model current partial assignment of variables of Value_type
     * @param cons linear constraint to evaluate
     * @return true iff @p cons is true in @p model
     */
    inline bool eval(Model<Value_type> const& model, Constraint_type const& cons) const
    {
        auto value = cons.rhs();
        auto [var_it, var_end] = vars(cons);
        auto [coef_it, coef_end] = coef(cons);
        for (; var_it != var_end; ++var_it, ++coef_it)
        {
            assert(coef_it != coef_end);
            assert(model.is_defined(*var_it));
            value -= *coef_it * model.value(*var_it);
        }
        return cons.pred()(Value_type{0}, value);
    }

    /** Given @p cons with exactly one unassigned variable, evaluate the rest of the constraint.
     *
     * Precondition: the first variable in @p cons is unassigned, the rest of variables is assigned
     * in @p model
     *
     * @param model current partial assignment of variables of Value_type
     * @param cons unit linear constraint with the first variable being the only unassigned variable
     * @return constant on the right-hand-side after evaluating all assigned variables in @p cons
     */
    inline Value_type implied_value(Model<Value_type> const& model,
                                    Constraint_type const& cons) const
    {
        auto value = cons.rhs();
        auto [var_it, var_end] = vars(cons);
        auto [coef_it, coef_end] = coef(cons);
        if (var_it == var_end)
        {
            return value;
        }
        assert(!model.is_defined(*var_it));

        ++var_it;
        ++coef_it;
        for (; var_it != var_end; ++var_it, ++coef_it)
        {
            assert(coef_it != coef_end);
            assert(model.is_defined(*var_it));
            value -= *coef_it * model.value(*var_it);
        }
        return value;
    }

private:
    using Constraint_hash = Linear_constraint_hash<Value_type>;
    using Constraint_equal = Linear_constraint_equal<Value_type>;
    using Constraint_set = std::unordered_set<Constraint_type, Constraint_hash, Constraint_equal>;

    // vector of variables of all linear constraints
    std::vector<int> variables;
    // vector of coefficients of all linear constraints
    std::vector<Value_type> coefficients;
    // map boolean variable -> linear constraint
    std::vector<Constraint_type> constraints;
    // set of constraints for deduplication
    Constraint_set cons_set;

    // find a constant by which the constraint will be multiplied in order to normalize coefficients
    template <std::ranges::range Var_range, std::ranges::range Coef_range>
    inline Value_type find_norm_constant(Var_range&& var_range, Coef_range&& coef_range) const
    {
        int min_var = var_range.front();
        auto min_coef = coef_range.front();

        auto var_it = std::begin(var_range);
        auto coef_it = std::begin(coef_range);
        for (; var_it != std::end(var_range); ++var_it, ++coef_it)
        {
            if (*var_it < min_var)
            {
                min_var = *var_it;
                min_coef = *coef_it;
            }
        }
        return Value_type{1} / min_coef;
    }

    // flip inequalities if mult is negative
    inline Order_predicate norm_pred(Value_type mult, Order_predicate pred) const
    {
        if (mult < Value_type{0})
        {
            switch (pred)
            {
            case Order_predicate::LT:
                return Order_predicate::LEQ;
            case Order_predicate::LEQ:
                return Order_predicate::LT;
            default:
                assert(pred == Order_predicate::EQ);
            }
        }
        return pred;
    }

    // copy constraint values multiplied by normalization constant `mult`
    template <std::ranges::range Var_range, std::ranges::range Coef_range>
    inline std::pair<Literal, std::pair<int, int>> add(Value_type mult, Var_range&& var_range,
                                                       Coef_range&& coef_range)
    {
        auto size = std::distance(std::begin(var_range), std::end(var_range));
        Literal lit{static_cast<int>(constraints.size())};
        std::pair<int, int> range{static_cast<int>(variables.size()),
                                  static_cast<int>(variables.size() + size)};

        variables.resize(range.second);
        coefficients.resize(range.second);

        std::copy(std::begin(var_range), std::end(var_range), variables.begin() + range.first);
        std::copy(std::begin(coef_range), std::end(coef_range), coefficients.begin() + range.first);

        // normalize coefficients of the constraint
        for (auto& c : coefficients | std::views::drop(range.first))
        {
            c *= mult;
        }
        return {lit, range};
    }
};

} // namespace perun

#endif // PREUN_LINEAR_CONSTRAINTS_H