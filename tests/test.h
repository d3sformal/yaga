#ifndef PERUN_TEST_H
#define PERUN_TEST_H

#include <algorithm>
#include <cassert>
#include <tuple>
#include <ranges>

#include "Literal.h"
#include "Clause.h"
#include "Linear_constraints.h"

namespace perun::test {

// structures to create ad-hoc linear constraints for tests
struct Dot_product {
    std::vector<int> vars;
    std::vector<double> coef;
};

struct Linear_predicate {
    Dot_product lhs;
    double rhs;
    Order_predicate pred;
    bool is_negation;
};

inline perun::Literal lit(int ord) 
{
    return perun::Literal{ord};
}

inline perun::Literal operator-(perun::Literal l)
{
    return l.negate();
}

template<typename... Args>
inline Clause clause(Args&&... args)
{
    return Clause{std::forward<Args>(args)...};
}

inline perun::Variable bool_var(int ord)
{
    return perun::Variable{ord, perun::Variable::boolean};
}

inline perun::Variable real_var(int ord)
{
    return perun::Variable{ord, perun::Variable::rational};
}

template<std::size_t... vars>
inline auto real_vars(std::integer_sequence<std::size_t, vars...>)
{
    return std::tuple{Variable{vars, Variable::rational}...};
}

template<int count>
inline auto real_vars()
{
    return real_vars(std::make_index_sequence<count>());
}

inline Dot_product operator*(double value, Variable var)
{
    return Dot_product{
        .vars = {var.ord()}, 
        .coef = {value}
    };
}

inline Dot_product operator*(Variable var, double value)
{
    assert(var.type() == Variable::rational);
    return value * var;
}

inline Dot_product operator+(Dot_product const& lhs, Dot_product const& rhs)
{
    auto res = lhs;
    res.vars.insert(res.vars.end(), rhs.vars.begin(), rhs.vars.end());
    res.coef.insert(res.coef.end(), rhs.coef.begin(), rhs.coef.end());
    return res;
}

inline Dot_product operator+(Dot_product const& lhs, Variable rhs)
{
    assert(rhs.type() == Variable::rational);
    auto res = lhs;
    res.vars.push_back(rhs.ord());
    res.coef.push_back(1);
    return res;
}

inline Dot_product operator+(Variable lhs, Dot_product const& rhs)
{
    return rhs + lhs;
}

inline Dot_product operator+(Variable lhs, Variable rhs)
{
    return Dot_product{
        .vars = {lhs.ord(), rhs.ord()},
        .coef = {1, 1}
    };
}

inline Dot_product operator-(Dot_product const& lhs, Dot_product const& rhs)
{
    auto res = lhs;
    res.vars.insert(res.vars.end(), rhs.vars.begin(), rhs.vars.end());
    res.coef.insert(res.coef.end(), rhs.coef.begin(), rhs.coef.end());
    for (auto& c : res.coef | std::views::drop(lhs.vars.size())) // negate rhs
    {
        c = -c;
    }
    return res;
}

inline Dot_product operator-(Dot_product const& lhs, Variable rhs)
{
    return lhs + Dot_product{.vars = {rhs.ord()}, .coef = {-1}};
}

inline Dot_product operator-(Variable lhs, Dot_product const& rhs)
{
    return Dot_product{.vars = {lhs.ord()}, .coef = {1}} - rhs;
}

inline Dot_product operator-(Variable lhs, Variable rhs)
{
    return Dot_product{.vars = {lhs.ord(), rhs.ord()}, .coef = {1, -1}};
}

inline Dot_product operator-(Variable var)
{
    assert(var.type() == Variable::rational);
    return Dot_product{
        .vars = {var.ord()},
        .coef = {-1}
    };
}

inline Linear_predicate operator<=(Dot_product const& lhs, double rhs)
{
    return Linear_predicate{
        .lhs = lhs,
        .rhs = rhs,
        .pred = Order_predicate::LEQ,
        .is_negation = false,
    };
}

inline Linear_predicate operator>=(Dot_product const& lhs, double rhs)
{
    return Linear_predicate{
        .lhs = lhs,
        .rhs = rhs,
        .pred = Order_predicate::LT,
        .is_negation = true,
    };
}

inline Linear_predicate operator<(Dot_product const& lhs, double rhs)
{
    return Linear_predicate{
        .lhs = lhs,
        .rhs = rhs,
        .pred = Order_predicate::LT,
        .is_negation = false,
    };
}

inline Linear_predicate operator>(Dot_product const& lhs, double rhs)
{
    return Linear_predicate{
        .lhs = lhs,
        .rhs = rhs,
        .pred = Order_predicate::LEQ,
        .is_negation = true,
    };
}

inline Linear_predicate operator==(Dot_product const& lhs, double rhs)
{
    return Linear_predicate{
        .lhs = lhs,
        .rhs = rhs,
        .pred = Order_predicate::EQ,
        .is_negation = false,
    };
}

inline Linear_predicate operator!=(Dot_product const& lhs, double rhs)
{
    return Linear_predicate{
        .lhs = lhs,
        .rhs = rhs,
        .pred = Order_predicate::EQ,
        .is_negation = true,
    };
}

inline Linear_predicate operator<=(Variable lhs, double rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_predicate{
        .lhs = Dot_product{.vars = {lhs.ord()}, .coef = {1}},
        .rhs = rhs,
        .pred = Order_predicate::LEQ,
        .is_negation = false,
    };
}

inline Linear_predicate operator>=(Variable lhs, double rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_predicate{
        .lhs = Dot_product{.vars = {lhs.ord()}, .coef = {1}},
        .rhs = rhs,
        .pred = Order_predicate::LT,
        .is_negation = true,
    };
}

inline Linear_predicate operator<(Variable lhs, double rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_predicate{
        .lhs = Dot_product{.vars = {lhs.ord()}, .coef = {1}},
        .rhs = rhs,
        .pred = Order_predicate::LT,
        .is_negation = false,
    };
}

inline Linear_predicate operator>(Variable lhs, double rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_predicate{
        .lhs = Dot_product{.vars = {lhs.ord()}, .coef = {1}},
        .rhs = rhs,
        .pred = Order_predicate::LEQ,
        .is_negation = true,
    };
}

inline Linear_predicate operator==(Variable lhs, double rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_predicate{
        .lhs = Dot_product{.vars = {lhs.ord()}, .coef = {1}},
        .rhs = rhs,
        .pred = Order_predicate::EQ,
        .is_negation = false,
    };
}

inline Linear_predicate operator!=(Variable lhs, double rhs)
{
    assert(lhs.type() == Variable::rational);
    return Linear_predicate{
        .lhs = Dot_product{.vars = {lhs.ord()}, .coef = {1}},
        .rhs = rhs,
        .pred = Order_predicate::EQ,
        .is_negation = true,
    };
}

// create a factory functor for linear constraints 
inline auto factory(Linear_constraints<double>& repository)
{
    return [rep_ptr = &repository](Linear_predicate const& val)
    {
        auto result = rep_ptr->make(val.lhs.vars, val.lhs.coef, val.pred, val.rhs);
        return val.is_negation ? result.negate() : result;
    };
}

template<typename Value>
inline Linear_constraint<Value> operator-(Linear_constraint<Value> const& cons)
{
    return cons.negate();
}

template<typename Value, typename... Tail>
inline Clause clause(Linear_constraint<Value> cons, Linear_constraint<Tail>... tail)
{
    return clause(cons.lit(), tail.lit()...);
}

}

#endif // PERUN_TEST_H