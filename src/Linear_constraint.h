#ifndef PERUN_LINEAR_CONSTRAINT_H
#define PERUN_LINEAR_CONSTRAINT_H

#include <cassert>
#include <concepts>
#include <functional>
#include <iterator>
#include <ostream>
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
    inline Linear_constraint()
        : position({0, 0}), predicate(Order_predicate::EQ), constant(0), constraints(nullptr)
    {
    }

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

    /** Check if this linear constraint represents a strict inequality (< or > or !=)
     *
     * @return true iff this is a constraint of type <, >, or !=
     */
    inline bool is_strict() const
    {
        return (lit().is_negation() && pred() == Order_predicate::LEQ) ||
               (!lit().is_negation() && pred() == Order_predicate::LT) ||
               (lit().is_negation() && pred() == Order_predicate::EQ);
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
 * @tparam Value type of constants in @p cons
 * @param model partial assignment of LRA variables
 * @param cons linear constraint to evaluate
 * @return true if @p cons is true in model, false if @p cons is false in model. None, if @p cons is
 * undefined.
 */
template <typename Value>
inline std::optional<bool> eval(Model<Value> const& model, Linear_constraint<Value> const& cons)
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

/** Print a linear constraint for testing
 *
 * @tparam Value type of constants in the linear constraint
 * @param out output stream
 * @param cons linear constraint to print
 * @return @p out
 */
template <typename Value>
inline std::ostream& operator<<(std::ostream& out, Linear_constraint<Value> const& cons)
{
    char const* delim = "";
    auto var_it = cons.vars().begin();
    auto coef_it = cons.coef().begin();
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        out << delim << *coef_it << " * " << Variable{*var_it, Variable::rational};
        delim = " + ";
    }

    if (!cons.lit().is_negation())
    {
        switch (cons.pred())
        {
        case Order_predicate::EQ:
            out << " = ";
            break;
        case Order_predicate::LT:
            out << " < ";
            break;
        case Order_predicate::LEQ:
            out << " <= ";
            break;
        }
    }
    else // negation
    {
        switch (cons.pred())
        {
        case Order_predicate::EQ:
            out << " != ";
            break;
        case Order_predicate::LT:
            out << " >= ";
            break;
        case Order_predicate::LEQ:
            out << " > ";
            break;
        }
    }
    out << cons.rhs();

    return out;
}

/** Hash functor for Linear_constraint that disregards order of variables.
 *
 * @tparam Value value type of coefficients in the constraint
 */
template <typename Value> class Linear_constraint_hash {
public:
    /** Create a hash of a linear constraint @p cons that ignores order of variables
     *
     * @param cons linear constraint
     * @return hash of @p cons such that any permutation of variables in @p cons produces the same
     * hash
     */
    std::size_t operator()(Linear_constraint<Value> const& cons) const
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
    std::hash<Value> coef_hash;
};

/** Equality compare functor for Linear_constraint that disregards order or variables.
 *
 * @tparam Value value type of coefficients in the constraint
 */
template <typename Value> class Linear_constraint_equal {
public:
    bool operator()(Linear_constraint<Value> const& lhs, Linear_constraint<Value> const& rhs) const
    {
        if (lhs.size() != rhs.size() || lhs.pred() != rhs.pred() || lhs.rhs() != rhs.rhs())
        {
            return false;
        }

        // check equality using a brute force algorithm
        auto lhs_var_it = lhs.vars().begin();
        auto lhs_coef_it = lhs.coef().begin();
        for (; lhs_var_it != lhs.vars().end(); ++lhs_var_it, ++lhs_coef_it)
        {
            assert(lhs_coef_it != lhs.coef().end());

            // find the variable in rhs
            auto rhs_var_it = std::find(rhs.vars().begin(), rhs.vars().end(), *lhs_var_it);
            if (rhs_var_it == rhs.vars().end())
            {
                return false;
            }

            // find the corresponding coefficient of the variable in rhs
            auto rhs_coef_it = rhs.coef().begin() + std::distance(rhs.vars().begin(), rhs_var_it);
            if (*lhs_coef_it != *rhs_coef_it)
            {
                return false;
            }
        }
        return true;
    }
};

} // namespace perun

#endif // PERUN_LINEAR_CONSTRAINT_H