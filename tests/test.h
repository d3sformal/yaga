#ifndef PERUN_TEST_H
#define PERUN_TEST_H

#include <algorithm>
#include <cassert>
#include <tuple>
#include <ranges>

#include "test_expr.h"
#include "Literal.h"
#include "Clause.h"
#include "Linear_constraints.h"

namespace perun::test {

inline perun::Literal lit(int ord) 
{
    return perun::Literal{ord};
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

// create a tuple of real variables
template<std::size_t... vars>
inline auto real_vars(std::integer_sequence<std::size_t, vars...>)
{
    return std::tuple{Variable{vars, Variable::rational}...};
}

// create a tuple of real variables
template<int count>
inline auto real_vars()
{
    return real_vars(std::make_index_sequence<count>());
}

// create clause from a list of linear constraints
template<typename Value, typename... Tail>
inline Clause clause(Linear_constraint<Value> cons, Linear_constraint<Tail>... tail)
{
    return clause(cons.lit(), tail.lit()...);
}

}

#endif // PERUN_TEST_H