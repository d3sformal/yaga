#ifndef PERUN_TEST_EXPR_H
#define PERUN_TEST_EXPR_H

#include <vector>
#include <algorithm>
#include <cassert>
#include <concepts>
#include <type_traits>
#include <unordered_map>
#include <map>
#include <ranges>

#include "Clause.h"
#include "Linear_constraints.h"
#include "Linear_arithmetic.h"

namespace perun::test {

template<typename T>
struct Is_arithmetic {
    inline static constexpr bool value = std::is_arithmetic_v<T>;
};

template<typename T>
    requires std::is_integral_v<T>
struct Is_arithmetic<Fraction<T>> {
    inline static constexpr bool value = true;
};

template<typename T>
concept Arithmetic = Is_arithmetic<T>::value;

// structures to create ad-hoc linear constraints for tests
// represents a linear polynomial
template<Arithmetic T>
struct Linear_polynomial {
    std::vector<int> vars;
    std::vector<T> coef;
    T constant;

    // conversion to other type
    template<typename To>
    explicit operator Linear_polynomial<To>() const
    {
        std::vector<To> new_coef(coef.size());
        std::copy(coef.begin(), coef.end(), new_coef.begin());
        return {.vars = vars, .coef = new_coef, .constant = static_cast<To>(constant)};
    }
};

template<Arithmetic T>
struct Linear_predicate {
    Linear_polynomial<T> lhs;
    Linear_polynomial<T> rhs;
    Order_predicate pred;
    bool is_negation;
};

// create linear polynomial from a variable
inline Linear_polynomial<Linear_arithmetic::Rational> poly(Variable var)
{
    assert(var.type() == Variable::rational);
    return {
        .vars = {var.ord()},
        .coef = {Linear_arithmetic::Rational{1}},
        .constant = Linear_arithmetic::Rational{0}
    };
}

// create linear polynomial from a constant
template<Arithmetic T>
inline Linear_polynomial<T> poly(T value)
{
    return {
        .vars = std::vector<int>{},
        .coef = std::vector<T>{},
        .constant = value
    };
}

// combine two linear polynomials using a binary operator to combine coefficients of variables
template<Arithmetic L, Arithmetic R, typename Bin_op>
inline Linear_polynomial<std::common_type_t<L, R>> 
combine(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs, Bin_op&& op)
{
    using Common_type = std::common_type_t<L, R>;

    std::map<int, Common_type> values;
    // add lhs
    {
        auto var_it = lhs.vars.begin();
        auto coef_it = lhs.coef.begin();
        for (; var_it != lhs.vars.end(); ++var_it, ++coef_it)
        {
            values.insert({*var_it, static_cast<Common_type>(*coef_it)});
        }
    }
    // add rhs
    {
        auto var_it = rhs.vars.begin();
        auto coef_it = rhs.coef.begin();
        for (; var_it != rhs.vars.end(); ++var_it, ++coef_it)
        {
            auto [it, _] = values.insert({*var_it, Common_type{0}});
            it->second = op(it->second, static_cast<Common_type>(*coef_it));
        }
    }

    auto vars = std::views::keys(values);
    auto coef = std::views::values(values);
    return {
        .vars = std::vector<int>{vars.begin(), vars.end()},
        .coef = std::vector<Common_type>{coef.begin(), coef.end()},
        .constant = op(static_cast<Common_type>(lhs.constant), static_cast<Common_type>(rhs.constant)),
    };
}

// create a linear polynomial from a constant multiple of a variable
template<Arithmetic T>
inline Linear_polynomial<Linear_arithmetic::Rational> operator*(T value, Variable var)
{
    return {
        .vars = {var.ord()},
        .coef = {value},
        .constant = Linear_arithmetic::Rational{0},
    };
}

// create a linear polynomial from a constant multiple of a variable
template<Arithmetic T>
inline auto operator*(Variable var, T value)
{
    assert(var.type() == Variable::rational);
    return value * var;
}

// add linear polynomials
template<Arithmetic L, Arithmetic R>
inline auto operator+(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    return combine(lhs, rhs, [](auto l, auto r) { return l + r; });
}

// add a 1 * variable to a linear polynomial 
template<Arithmetic T>
inline auto operator+(Linear_polynomial<T> const& lhs, Variable rhs)
{
    return lhs + poly(rhs);
}

// add a 1 * variable to a linear polynomial 
template<Arithmetic T>
inline auto operator+(Variable lhs, Linear_polynomial<T> const& rhs)
{
    return rhs + lhs;
}

// add constant to linear polynomial
template<Arithmetic L, Arithmetic R>
inline auto operator+(Linear_polynomial<L> const& lhs, R rhs)
{
    return lhs + poly(rhs);
}

// add constant to linear polynomial
template<Arithmetic L, Arithmetic R>
inline auto operator+(L lhs, Linear_polynomial<R> const& rhs)
{
    return poly(lhs) + rhs;
}

// add a constant to a variable
template<Arithmetic R>
inline auto operator+(Variable lhs, R rhs)
{
    return poly(lhs) + poly(rhs);
}

// add a constant to a variable
template<Arithmetic L>
inline auto operator+(L lhs, Variable rhs)
{
    return poly(lhs) + poly(rhs);
}

// create linear polynomial from addition of two variables
inline auto operator+(Variable lhs, Variable rhs)
{
    return poly(lhs) + poly(rhs);
}

// subtract linear polynomials
template<Arithmetic L, Arithmetic R>
inline auto operator-(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    return combine(lhs, rhs, [](auto l, auto r) { return l - r; });
}

// subtract 1 * variable from a linear polynomial
template<Arithmetic T>
inline auto operator-(Linear_polynomial<T> const& lhs, Variable rhs)
{
    return lhs - poly(rhs);
}

// subtract linear polynomial from 1 * variable
template<Arithmetic T>
inline auto operator-(Variable lhs, Linear_polynomial<T> const& rhs)
{
    return poly(lhs) - rhs;
}

// subtract a constant from linear polynomial
template<Arithmetic L, Arithmetic R>
inline auto operator-(Linear_polynomial<L> const& lhs, R rhs)
{
    return lhs - poly(rhs);
}

// subtract linear polynomial from a constant
template<Arithmetic L, Arithmetic R>
inline auto operator-(L lhs, Linear_polynomial<R> const& rhs)
{
    return poly(lhs) - rhs;
}

// create linear polynomial from a subtraction of two variables
inline auto operator-(Variable lhs, Variable rhs)
{
    assert(lhs != rhs);
    return poly(lhs) - poly(rhs);
}

// create linear polynomial from -1 * variable
inline auto operator-(Variable var)
{
    assert(var.type() == Variable::rational);
    return Linear_polynomial<Linear_arithmetic::Rational>{
        .vars = {var.ord()},
        .coef = {-1},
        .constant = Linear_arithmetic::Rational{0}
    };
}

// create a linear predicate `lhs <= rhs`
template<Arithmetic L, Arithmetic R>
inline Linear_predicate<std::common_type_t<L, R>> operator<=(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::leq,
        .is_negation = false,
    };
}

// create a linear predicate `lhs >= rhs`
template<Arithmetic L, Arithmetic R>
inline Linear_predicate<std::common_type_t<L, R>> operator>=(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::lt,
        .is_negation = true,
    };
}

// create a linear predicate `lhs < rhs`
template<Arithmetic L, Arithmetic R>
inline Linear_predicate<std::common_type_t<L, R>> operator<(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::lt,
        .is_negation = false,
    };
}

// create a linear predicate `lhs > rhs`
template<Arithmetic L, Arithmetic R>
inline Linear_predicate<std::common_type_t<L, R>> operator>(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::leq,
        .is_negation = true,
    };
}

// create a linear predicate `lhs = rhs`
template<Arithmetic L, Arithmetic R>
inline Linear_predicate<std::common_type_t<L, R>> operator==(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::eq,
        .is_negation = false,
    };
}

// create a linear predicate `lhs != rhs`
template<Arithmetic L, Arithmetic R>
inline Linear_predicate<std::common_type_t<L, R>> operator!=(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::eq,
        .is_negation = true,
    };
}

// create a linear predicate `lhs <= rhs` if rhs is a constant
template<Arithmetic T, Arithmetic R>
inline auto operator<=(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs <= poly(rhs);
}

// create a linear predicate `lhs >= rhs` if rhs is a constant
template<Arithmetic T, Arithmetic R>
    requires std::is_convertible_v<R, T>
inline auto operator>=(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs >= poly(rhs);
}

// create a linear predicate `lhs < rhs` if rhs is a constant
template<Arithmetic T, Arithmetic R>
    requires std::is_convertible_v<R, T>
inline auto operator<(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs < poly(rhs);
}

// create a linear predicate `lhs > rhs` if rhs is a constant
template<Arithmetic T, Arithmetic R>
    requires std::is_convertible_v<R, T>
inline auto operator>(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs > poly(rhs);
}

// create a linear predicate `lhs = rhs` if rhs is a constant
template<Arithmetic T, Arithmetic R>
    requires std::is_convertible_v<R, T>
inline auto operator==(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs == poly(rhs);
}

// create a linear predicate `lhs != rhs` if rhs is a constant
template<Arithmetic T, Arithmetic R>
    requires std::is_convertible_v<R, T>
inline auto operator!=(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs != poly(rhs);
}

template<Arithmetic T>
inline auto operator<=(Linear_polynomial<T> const& lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return lhs <= poly(rhs);
}

template<Arithmetic T>
inline auto operator<(Linear_polynomial<T> const& lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return lhs < poly(rhs);
}

template<Arithmetic T>
inline auto operator>(Linear_polynomial<T> const& lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return lhs > poly(rhs);
}

template<Arithmetic T>
inline auto operator>=(Linear_polynomial<T> const& lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return lhs >= poly(rhs);
}

template<Arithmetic T>
inline auto operator==(Linear_polynomial<T> const& lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return lhs == poly(rhs);
}

template<Arithmetic T>
inline auto operator!=(Linear_polynomial<T> const& lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return lhs != poly(rhs);
}

template<Arithmetic T>
inline auto operator<=(Variable lhs, Linear_polynomial<T> const& rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) <= rhs;
}

template<Arithmetic T>
inline auto operator<(Variable lhs, Linear_polynomial<T> const& rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) < rhs;
}

template<Arithmetic T>
inline auto operator>=(Variable lhs, Linear_polynomial<T> const& rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) >= rhs;
}

template<Arithmetic T>
inline auto operator>(Variable lhs, Linear_polynomial<T> const& rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) > rhs;
}

template<Arithmetic T>
inline auto operator==(Variable lhs, Linear_polynomial<T> const& rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) == rhs;
}

template<Arithmetic T>
inline auto operator!=(Variable lhs, Linear_polynomial<T> const& rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) != rhs;
}

template<Arithmetic T>
inline auto operator<=(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) <= poly(rhs);
}

template<Arithmetic T>
inline auto operator>=(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) >= poly(rhs);
}

template<Arithmetic T>
inline auto operator<(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) < poly(rhs);
}

template<Arithmetic T>
inline auto operator>(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) > poly(rhs);
}

template<Arithmetic T>
inline auto operator==(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) == poly(rhs);
}

template<Arithmetic T>
inline auto operator<=(T lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return poly(lhs) <= poly(rhs);
}

template<Arithmetic T>
inline auto operator<(T lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return poly(lhs) < poly(rhs);
}

template<Arithmetic T>
inline auto operator>(T lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return poly(lhs) > poly(rhs);
}

template<Arithmetic T>
inline auto operator>=(T lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return poly(lhs) >= poly(rhs);
}

template<Arithmetic T>
inline auto operator==(T lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return poly(lhs) == poly(rhs);
}

template<Arithmetic T>
inline auto operator!=(T lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    return poly(lhs) != poly(rhs);
}

template<Arithmetic T>
inline auto operator!=(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) != poly(rhs);
}

inline auto operator<=(Variable lhs, Variable rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) <= poly(rhs);
}

inline auto operator<(Variable lhs, Variable rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) < poly(rhs);
}

inline auto operator>(Variable lhs, Variable rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) > poly(rhs);
}

inline auto operator>=(Variable lhs, Variable rhs)
{
    assert(lhs.type() == Variable::rational);
    return poly(lhs) >= poly(rhs);
}

// create a factory functor for linear constraints 
template<Arithmetic T>
inline auto factory(Linear_constraints<T>& repository)
{
    return [rep_ptr = &repository]<std::convertible_to<T> R>(Linear_predicate<R> const& val)
    {
        // move right-hand-side to left-hand-side
        auto poly = val.lhs - val.rhs;
        auto cons = rep_ptr->make(poly.vars, poly.coef, val.pred, val.rhs.constant - val.lhs.constant);
        return val.is_negation ? cons.negate() : cons;
    };
}

// create a factory functor for linear constraints in the LRA plugin
inline auto factory(Linear_arithmetic& plugin, Trail& trail)
{
    return [plugin_ptr = &plugin, trail_ptr = &trail]<std::convertible_to<Linear_arithmetic::Rational> T>(Linear_predicate<T> const& val) 
    {
        // move right-hand-side to left-hand-side
        auto poly = val.lhs - val.rhs;
        auto cons = plugin_ptr->constraint(*trail_ptr, poly.vars, poly.coef, val.pred, val.rhs.constant - val.lhs.constant);
        return val.is_negation ? cons.negate() : cons;
    };
}

}

#endif // PERUN_TEST_EXPR_H