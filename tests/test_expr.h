#include <vector>
#include <algorithm>
#include <cassert>
#include <concepts>
#include <type_traits>
#include <unordered_map>
#include <ranges>

#include "Clause.h"
#include "Linear_constraints.h"
#include "Linear_arithmetic.h"

namespace perun::test {

// structures to create ad-hoc linear constraints for tests
// represents a linear polynomial
template<typename T>
    requires std::is_arithmetic_v<T>
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

template<typename T>
    requires std::is_arithmetic_v<T>
struct Linear_predicate {
    Linear_polynomial<T> lhs;
    Linear_polynomial<T> rhs;
    Order_predicate pred;
    bool is_negation;
};

// conversion
// create a linear polynomial from a constant multiple of a variable
template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_polynomial<T> operator*(T value, Variable var)
{
    return {
        .vars = {var.ord()}, 
        .coef = {value},
        .constant = T{0},
    };
}

// create a linear polynomial from a constant multiple of a variable
template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_polynomial<T> operator*(Variable var, T value)
{
    assert(var.type() == Variable::rational);
    return value * var;
}

// add linear polynomials
template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_polynomial<T> operator+(Linear_polynomial<T> const& lhs, Linear_polynomial<T> const& rhs)
{
    std::unordered_map<int, T> result;
    for (auto poly_ptr : {&lhs, &rhs})
    {
        auto var_it = poly_ptr->vars.begin();
        auto coef_it = poly_ptr->coef.begin();
        for (; var_it != poly_ptr->vars.end(); ++var_it, ++coef_it)
        {
            auto [it, _] = result.insert({*var_it, T{0}});
            it->second += *coef_it;
        }
    }

    auto vars = std::views::keys(result);
    auto coef = std::views::values(result);
    return {
        .vars = std::vector<int>{vars.begin(), vars.end()},
        .coef = std::vector<T>{coef.begin(), coef.end()},
        .constant = lhs.constant + rhs.constant,
    };
}

// add a 1 * variable to a linear polynomial 
template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_polynomial<T> operator+(Linear_polynomial<T> const& lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    auto res = lhs;
    auto it = std::find(res.vars.begin(), res.vars.end(), rhs.ord());
    if (it == res.vars.end())
    {
        res.vars.push_back(rhs.ord());
        res.coef.push_back(T{1});
        return res;
    }
    auto coef_it = res.coef.begin() + std::distance(res.vars.begin(), it);
    *coef_it = *coef_it + 1;
    
    return res;
}

// add a 1 * variable to a linear polynomial 
template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_polynomial<T> operator+(Variable lhs, Linear_polynomial<T> const& rhs)
{
    return rhs + lhs;
}

// create linear polynomial from addition of two variables
inline Linear_polynomial<double> operator+(Variable lhs, Variable rhs)
{
    return {
        .vars = {lhs.ord(), rhs.ord()},
        .coef = {1, 1},
        .constant = 0,
    };
}

// subtract two linear polynomials
template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_polynomial<T> operator-(Linear_polynomial<T> const& lhs, Linear_polynomial<T> const& rhs)
{
    T mult{1};
    std::unordered_map<int, T> result;
    for (auto poly_ptr : {&lhs, &rhs})
    {
        auto var_it = poly_ptr->vars.begin();
        auto coef_it = poly_ptr->coef.begin();
        for (; var_it != poly_ptr->vars.end(); ++var_it, ++coef_it)
        {
            auto [it, _] = result.insert({*var_it, T{0}});
            it->second += *coef_it * mult;
        }
        mult = T{-1};
    }

    auto vars = std::views::keys(result);
    auto coef = std::views::values(result);
    return {
        .vars = std::vector<int>{vars.begin(), vars.end()},
        .coef = std::vector<T>{coef.begin(), coef.end()},
        .constant = lhs.constant() - rhs.constant(),
    };
}

// subtract 1 * variable from a linear polynomial
template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_polynomial<T> operator-(Linear_polynomial<T> const& lhs, Variable rhs)
{
    return lhs + Linear_polynomial<T>{.vars = {rhs.ord()}, .coef = {T{-1}}, .constant = T{0}};
}

// subtract linear polynomial from 1 * variable
template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_polynomial<T> operator-(Variable lhs, Linear_polynomial<T> const& rhs)
{
    return Linear_polynomial<T>{.vars = {lhs.ord()}, .coef = {T{1}}} - rhs;
}

// create linear polynomial from a subtraction of two variables
inline Linear_polynomial<double> operator-(Variable lhs, Variable rhs)
{
    assert(lhs != rhs);
    return {.vars = {lhs.ord(), rhs.ord()}, .coef = {1, -1}, .constant = 0.0};
}

// create linear polynomial from -1 * variable
inline Linear_polynomial<double> operator-(Variable var)
{
    assert(var.type() == Variable::rational);
    return {
        .vars = {var.ord()},
        .coef = {-1},
        .constant = 0
    };
}

// create a linear predicate `lhs <= rhs`
template<typename L, typename R>
    requires std::is_arithmetic_v<L> && std::is_arithmetic_v<R>
inline Linear_predicate<std::common_type_t<L, R>> operator<=(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::LEQ,
        .is_negation = false,
    };
}

// create a linear predicate `lhs >= rhs`
template<typename L, typename R>
    requires std::is_arithmetic_v<L> && std::is_arithmetic_v<R>
inline Linear_predicate<std::common_type_t<L, R>> operator>=(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::LT,
        .is_negation = true,
    };
}

// create a linear predicate `lhs < rhs`
template<typename L, typename R>
    requires std::is_arithmetic_v<L> && std::is_arithmetic_v<R>
inline Linear_predicate<std::common_type_t<L, R>> operator<(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::LT,
        .is_negation = false,
    };
}

// create a linear predicate `lhs > rhs`
template<typename L, typename R>
    requires std::is_arithmetic_v<L> && std::is_arithmetic_v<R>
inline Linear_predicate<std::common_type_t<L, R>> operator>(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::LEQ,
        .is_negation = true,
    };
}

// create a linear predicate `lhs = rhs`
template<typename L, typename R>
    requires std::is_arithmetic_v<L> && std::is_arithmetic_v<R>
inline Linear_predicate<std::common_type_t<L, R>> operator==(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::EQ,
        .is_negation = false,
    };
}

// create a linear predicate `lhs != rhs`
template<typename L, typename R>
    requires std::is_arithmetic_v<L> && std::is_arithmetic_v<R>
inline Linear_predicate<std::common_type_t<L, R>> operator!=(Linear_polynomial<L> const& lhs, Linear_polynomial<R> const& rhs)
{
    using Result_type = Linear_polynomial<std::common_type_t<L, R>>;
    return {
        .lhs = static_cast<Result_type>(lhs),
        .rhs = static_cast<Result_type>(rhs),
        .pred = Order_predicate::EQ,
        .is_negation = true,
    };
}

// create a linear predicate `lhs <= rhs` if rhs is a constant
template<typename T, typename R>
    requires std::is_arithmetic_v<T> && std::is_arithmetic_v<R> && std::is_convertible_v<R, T>
inline Linear_predicate<T> operator<=(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs <= Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = static_cast<T>(rhs)};
}

// create a linear predicate `lhs >= rhs` if rhs is a constant
template<typename T, typename R>
    requires std::is_arithmetic_v<T> && std::is_arithmetic_v<R> && std::is_convertible_v<R, T>
inline Linear_predicate<T> operator>=(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs >= Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = static_cast<T>(rhs)};
}

// create a linear predicate `lhs < rhs` if rhs is a constant
template<typename T, typename R>
    requires std::is_arithmetic_v<T> && std::is_arithmetic_v<R> && std::is_convertible_v<R, T>
inline Linear_predicate<T> operator<(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs < Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = static_cast<T>(rhs)};
}

// create a linear predicate `lhs > rhs` if rhs is a constant
template<typename T, typename R>
    requires std::is_arithmetic_v<T> && std::is_arithmetic_v<R> && std::is_convertible_v<R, T>
inline Linear_predicate<T> operator>(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs > Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = static_cast<T>(rhs)};
}

// create a linear predicate `lhs = rhs` if rhs is a constant
template<typename T, typename R>
    requires std::is_arithmetic_v<T> && std::is_arithmetic_v<R> && std::is_convertible_v<R, T>
inline Linear_predicate<T> operator==(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs == Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = static_cast<T>(rhs)};
}

// create a linear predicate `lhs != rhs` if rhs is a constant
template<typename T, typename R>
    requires std::is_arithmetic_v<T> && std::is_arithmetic_v<R> && std::is_convertible_v<R, T>
inline Linear_predicate<T> operator!=(Linear_polynomial<T> const& lhs, R rhs)
{
    return lhs != Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = static_cast<T>(rhs)};
}

template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_predicate<T> operator<=(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_polynomial<T>{.vars = {lhs.ord()}, .coef = {T{1}}, .constant = T{0}} <= Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = rhs};
}

template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_predicate<T> operator>=(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_polynomial<T>{.vars = {lhs.ord()}, .coef = {T{1}}, .constant = T{0}} >= Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = rhs};
}

template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_predicate<T> operator<(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_polynomial<T>{.vars = {lhs.ord()}, .coef = {T{1}}, .constant = T{0}} < Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = rhs};
}

template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_predicate<T> operator>(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_polynomial<T>{.vars = {lhs.ord()}, .coef = {T{1}}, .constant = T{0}} > Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = rhs};
}

template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_predicate<T> operator==(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_polynomial<T>{.vars = {lhs.ord()}, .coef = {T{1}}, .constant = T{0}} == Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = rhs};
}

template<typename T>
    requires std::is_arithmetic_v<T>
inline Linear_predicate<T> operator!=(Variable lhs, T rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_polynomial<T>{.vars = {lhs.ord()}, .coef = {T{1}}, .constant = T{0}} != Linear_polynomial<T>{.vars = {}, .coef = {}, .constant = rhs};
}

// normalize the polynomial in a linear predicate by moving all non-constant terms on the right-hand-side to the left-hand-side
template<typename T, typename R>
    requires std::is_arithmetic_v<T> && std::is_arithmetic_v<R> && std::convertible_to<R, T>
inline std::vector<std::pair<int, T>> normalize(Linear_predicate<R> const& val)
{
    std::vector<std::pair<int, T>> poly;

    // add all variables and coefficients
    T mult{1};
    for (auto poly_ptr : {&val.lhs, &val.rhs})
    {
        auto var_it = poly_ptr->vars.begin();
        auto coef_it = poly_ptr->coef.begin();
        for (; var_it != poly_ptr->vars.end(); ++var_it, ++coef_it)
        {
            poly.push_back({*var_it, static_cast<T>(*coef_it) * mult});
        }
        mult = T{-1};
    }

    // combine coefficients of variables
    std::sort(poly.begin(), poly.end());
    if (poly.size() > 1)
    {
        auto out_it = poly.begin();
        for (auto next = poly.begin(), it = next++; next != poly.end(); ++next, ++it)
        {
            if (next->first != it->first)
            {
                *out_it++ = *it;
            }
            else
            {
                next->second += it->second;
            }
        }
        *out_it++ = poly.back();
        poly.erase(out_it, poly.end());
    }
    return poly;
}

// create a factory functor for linear constraints 
template<typename T>
    requires std::is_arithmetic_v<T>
inline auto factory(Linear_constraints<T>& repository)
{
    return [rep_ptr = &repository]<std::convertible_to<T> R>(Linear_predicate<R> const& val)
    {
        // move right-hand-side to left-hand-side
        auto poly = normalize<T>(val);
        auto cons = rep_ptr->make(std::views::keys(poly), std::views::values(poly), val.pred, val.rhs.constant - val.lhs.constant);
        return val.is_negation ? cons.negate() : cons;
    };
}

// create a factory functor for linear constraints in the LRA plugin
inline auto factory(Linear_arithmetic& plugin)
{
    return [plugin_ptr = &plugin]<std::convertible_to<Linear_arithmetic::Value_type> T>(Linear_predicate<T> const& val) 
    {
        // move right-hand-side to left-hand-side
        auto poly = normalize<T>(val);
        auto cons = plugin_ptr->constraint(std::views::keys(poly), std::views::values(poly), val.pred, val.rhs.constant - val.lhs.constant);
        return val.is_negation ? cons.negate() : cons;
    };
}

}