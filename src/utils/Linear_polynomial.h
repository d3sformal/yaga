#ifndef YAGA_LINEAR_POLYNOMIAL_H
#define YAGA_LINEAR_POLYNOMIAL_H

#include <vector>

#include "Rational.h"
#include "Trail.h"
#include "Variable.h"

namespace yaga::utils
{

struct Linear_polynomial {
    std::vector<int> vars;
    std::vector<Rational> coef;
    Rational constant = 0;

    void add(Linear_polynomial &&);
    void sub(Linear_polynomial &&);
    void negate();
    void sort(Trail&);
    void subtract_var(Variable v);
};

} // namespace yaga::utils

#endif // YAGA_LINEAR_POLYNOMIAL_H
