#ifndef PERUN_LRA_CONFLICT_ANALYSIS_H
#define PERUN_LRA_CONFLICT_ANALYSIS_H

#include <algorithm>
#include <cassert>
#include <optional>
#include <ostream>
#include <tuple>
#include <vector>

#include "Bounds.h"
#include "Clause.h"
#include "Fraction.h"
#include "Linear_constraint.h"
#include "Trail.h"

namespace perun {

namespace detail {

template <typename T> struct Linear_polynomial {
    using Models = Theory_models<T>;
    using Variable_coefficient = std::pair<int, T>;

    // pairs of variable and coefficient
    std::vector<Variable_coefficient> variables;
    // constant term
    T constant;

    inline auto begin() { return variables.begin(); }
    inline auto end() { return variables.end(); }
    inline auto begin() const { return variables.begin(); }
    inline auto end() const { return variables.end(); }
    inline auto size() const { return variables.size(); }
    inline bool empty() const { return variables.empty(); }

    /** Add up all coefficients that belong to the same variable and remove variables with
     * 0 coefficient.
     */
    void normalize()
    {
        // sort by variable
        std::sort(begin(), end(), [&](auto lhs, auto rhs) { return lhs.first < rhs.first; });

        // combine coefficients if they belong to the same variable
        auto out_it = begin();
        for (auto [var, coef] : *this | std::views::drop(1))
        {
            if (out_it->first != var)
            {
                if (out_it->second != 0) // drop variables with 0 coefficient
                {
                    ++out_it;
                }
                out_it->first = var;
                out_it->second = coef;
            }
            else
            {
                out_it->second += coef;
            }
        }

        if (!empty() && out_it->second != 0) // drop variables with 0 coefficient
        {
            ++out_it;
        }
        variables.erase(out_it, end());
    }

    /** Evaluate the polynomial except for the first variable
     *
     * @param models partial assignment of variables
     * @return
     */
    T implied_value(Models models) const
    {
        assert(!empty());

        auto var_coef = begin()->second;
        auto bound = -constant;
        for (auto [ord, coef] : *this | std::views::drop(1))
        {
            assert(models.owned().is_defined(ord));
            bound -= coef * models.owned().value(ord);
        }
        return bound / var_coef;
    }
};

/** Print linear polynomial to an output stream
 *
 * @param out output stream
 * @param poly linear polynomial to print
 * @return @p out
 */
template <typename T> std::ostream& operator<<(std::ostream& out, Linear_polynomial<T> const& poly)
{
    char const* sep = "";
    for (auto [var_ord, coef] : poly)
    {
        out << sep;
        if (coef != 1)
        {
            out << coef << " * ";
        }
        out << Variable{var_ord, Variable::rational};
        sep = " + ";
    }
    if (poly.constant != 0)
    {
        out << sep << poly.constant;
    }
    return out;
}

} // namespace detail

class Linear_arithmetic;

class Fourier_motzkin_elimination {
public:
    using Rational = Fraction<int>;
    using Models = Theory_models<Rational>;
    using Constraint = Linear_constraint<Rational>;
    using Polynomial = detail::Linear_polynomial<Rational>;
    using Variable_coefficient = std::pair<int, Rational>;

    inline explicit Fourier_motzkin_elimination(Linear_arithmetic* lra) : lra(lra) {}

    /** Set current constraint to @p cons
     *
     * @param cons linear constraint
     */
    void init(Constraint const& cons);

    /** Set current constraint to the polynomial of @p cons multiplied by @p mult with predicate
     * @p pred
     *
     * @param cons linear constraint
     * @param pred predicate of the current constraint (predicate of @p cons is ignored)
     * @param mult constant by which we multiply linear polynomial from @p cons
     */
    void init(Constraint const& cons, Order_predicate pred, Rational mult);

    /** Fourier-Motzkin elimination of the first variable in current constraint.
     *
     * If current constraint is `L <= x` and @p cons is `x <= U` (or vice versa), derive `L <= U`
     * where `x` is the first variable in current constraint.
     *
     * @param cons linear constraint
     */
    void resolve(Constraint const& cons);

    /** Create a linear constraint from current derivation and propagate it to the @p trail
     *
     * @param trail current solver trail
     * @return FM derivation
     */
    Constraint finish(Trail& trail);

private:
    // polynomial of the currently derived constraint
    Polynomial poly;
    // predicate of the currently derived constraint
    Order_predicate pred = Order_predicate::eq;
    // LRA plugin
    Linear_arithmetic* lra;

    // check if a linear constraint implies a lower bound for a variable with coefficient `coef`
    inline bool is_lower_bound(Rational coef, Order_predicate pred, bool is_negation) const
    {
        return pred == Order_predicate::eq || (coef < 0 && !is_negation) ||
               (coef > 0 && is_negation);
    }

    // check if a linear constraint implies an upper bound for a variable with coefficient `coef`
    inline bool is_upper_bound(Rational coef, Order_predicate pred, bool is_negation) const
    {
        return pred == Order_predicate::eq || (coef > 0 && !is_negation) ||
               (coef < 0 && is_negation);
    }

    // check if current constraint implies a lower bound
    inline bool is_lower_bound() const
    {
        assert(!poly.empty());
        return is_lower_bound(poly.variables.front().second, pred, false);
    }

    // check if current constraint implies an upper bound
    inline bool is_upper_bound() const
    {
        assert(!poly.empty());
        return is_upper_bound(poly.variables.front().second, pred, false);
    }
};

class Bound_conflict_analysis {
public:
    using Rational = Fraction<int>;
    using Models = Theory_models<Rational>;
    using Constraint = Linear_constraint<Rational>;
    using Polynomial = detail::Linear_polynomial<Rational>;
    using Variable_bounds = Bounds<Rational>;

    inline Bound_conflict_analysis(Linear_arithmetic* lra) : lra(lra), fm(lra) {}

    /** Check if there is a bound conflict (i.e., `L <= x` and `x <= U` and `L > U` or similar
     * conflicts with strict bounds)
     *
     * @param trail current solver trail
     * @param bounds implied bounds for a variable
     * @return conflict clause if there is a bound conflict. None, otherwise.
     */
    std::optional<Clause> analyze(Trail& trail, Variable_bounds& bounds);

private:
    Linear_arithmetic* lra;
    Fourier_motzkin_elimination fm;
};

class Inequality_conflict_analysis {
public:
    using Rational = Fraction<int>;
    using Models = Theory_models<Rational>;
    using Constraint = Linear_constraint<Rational>;
    using Polynomial = detail::Linear_polynomial<Rational>;
    using Variable_bounds = Bounds<Rational>;

    inline Inequality_conflict_analysis(Linear_arithmetic* lra) : lra(lra), fm(lra) {}

    /** Check if there is an inequality conflict - i.e., `L <= x` and `x <= U` and `x != D`
     * where L, U, D evaluate to the same value in @p trail
     *
     * @param trail current solver trail
     * @param bounds implied bounds for a variable
     * @return conflict clause if there is an inequality conflict. None, otherwise.
     */
    std::optional<Clause> analyze(Trail& trail, Variable_bounds& bounds);

private:
    Linear_arithmetic* lra;
    Fourier_motzkin_elimination fm;
};

} // namespace perun

#endif // PERUN_LRA_CONFLICT_ANALYSIS_H