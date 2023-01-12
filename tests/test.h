#ifndef PERUN_TEST_H_
#define PERUN_TEST_H_

#include "Literal.h"
#include "Clause.h"

namespace perun::test {

inline perun::Literal lit(int ord) 
{
    return perun::Literal{ord};
}

inline perun::Literal operator-(perun::Literal l)
{
    return l.negate();
}

inline perun::Variable bool_var(int ord)
{
    return perun::Variable{ord, perun::Variable::boolean};
}

template<typename... Args>
inline perun::Clause clause(Args&&... args)
{
    return perun::Clause{std::forward<Args>(args)...};
}

}

#endif // PERUN_TEST_H_