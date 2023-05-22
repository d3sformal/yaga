#ifndef YAGA_LRA_CONFLICT_ANALYSIS_H
#define YAGA_LRA_CONFLICT_ANALYSIS_H

#include <algorithm>
#include <cassert>
#include <optional>
#include <ostream>
#include <tuple>
#include <vector>

#include "Bounds.h"
#include "Clause.h"
#include "Rational.h"
#include "Linear_constraint.h"
#include "Trail.h"
#include "Variable_bounds.h"

namespace yaga {

namespace detail {

template <typename T> struct Linear_polynomial {
    using Models = Theory_models<T>;
    using Variable_coefficient = std::pair<int, T>;

    // pairs of variable and coefficient
    std::vector<Variable_coefficient> variables;
    // constant term
    T constant{0};

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
    T implied_value(Models const& models) const
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

class Fm_elimination {
public:
    using Models = Theory_models<Rational>;
    using Constraint = Linear_constraint<Rational>;
    using Polynomial = detail::Linear_polynomial<Rational>;
    using Variable_coefficient = std::pair<int, Rational>;

    inline explicit Fm_elimination(Linear_arithmetic* lra) : lra(lra) {}

    /** Create FM elimination starting with the constraint @p cons
     *
     * @param lra LRA plugin
     * @param cons linear constraint
     */
    inline Fm_elimination(Linear_arithmetic* lra, Constraint cons) : lra(lra) { init(cons); }

    /** Create FM elimination starting with the polynomial of @p cons multiplied by @p mult with
     * predicate @p pred
     *
     * @param lra LRA plugin
     * @param cons linear constraint
     * @param pred predicate of the constraint (actual predicate of @p cons is ignored)
     * @param mult constant by which we multiply linear polynomial from @p cons
     */
    inline Fm_elimination(Linear_arithmetic* lra, Constraint cons, Order_predicate pred,
                          Rational mult)
        : lra(lra)
    {
        init(cons, pred, mult);
    }

    // non-copyable
    Fm_elimination(Fm_elimination const&) = delete;
    Fm_elimination& operator=(Fm_elimination const&) = delete;

    // movable
    Fm_elimination(Fm_elimination&& other) = default;
    Fm_elimination& operator=(Fm_elimination&& other) = default;

    /** FM elimination of @p var using constraint derived from @p other FM elimination
     *
     * @param other other FM elimination
     * @param var rational variable ordinal to resolve
     */
    void resolve(Fm_elimination const& other, int var);

    /** Create a linear constraint from current derivation and propagate it to the @p trail
     *
     * @param trail current solver trail
     * @return FM derivation
     */
    Constraint finish(Trail& trail);

    /** Get current derived polynomial
     *
     * @return current linear polynomial
     */
    inline Polynomial& derived() { return poly; }
    inline Polynomial const& derived() const { return poly; }

    /** Get current predicate
     *
     * @return derived predicate
     */
    inline Order_predicate predicate() const { return pred; }

    /** Find predicate of the constraint after FM elimination
     *
     * @param first predicate of one constraint
     * @param second predicate of the other constraint
     * @return predicate of the combination (constraint after FM elimination)
     */
    Order_predicate combine(Order_predicate first, Order_predicate second) const;

private:
    // polynomial of the currently derived constraint
    Polynomial poly;
    // predicate of the currently derived constraint
    Order_predicate pred = Order_predicate::eq;
    // LRA plugin
    Linear_arithmetic* lra;

    /** Set current constraint to @p cons
     *
     * @param cons linear constraint
     */
    void init(Constraint const& cons);

    /** Set current constraint to the derived constraint from @p other elimination
     *
     * @param other other FM elimination
     */
    void init(Fm_elimination&& other);

    /** Set current constraint to the polynomial of @p cons multiplied by @p mult with predicate
     * @p pred
     *
     * @param cons linear constraint
     * @param pred predicate of the current constraint (predicate of @p cons is ignored)
     * @param mult constant by which we multiply linear polynomial from @p cons
     */
    void init(Constraint const& cons, Order_predicate pred, Rational mult);

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
};

/** Derive a conflict clause by eliminating all unassigned variables.
 */
class Lra_conflict_analysis {
public:
    using Models = Theory_models<Rational>;
    using Constraint = Linear_constraint<Rational>;
    using Polynomial = detail::Linear_polynomial<Rational>;

    inline Lra_conflict_analysis(Linear_arithmetic* lra) : lra(lra) {}

    /** Eliminate a variable using @p bound
     *
     * All unassigned variables in @p bound are eliminated using FM elimination and the old
     * constraints used for the elimination are added as assumptions to current conflict clause.
     *
     * @param models partial assignment of variables
     * @param bounds variable bounds
     * @param bound bound of a variable to eliminate
     * @return derived linear constraint of @p bound after eliminating all unassigned variables
     */
    Fm_elimination eliminate(Models const& models, Bounds& bounds,
                             Implied_value<Rational> const& bound);

    /** Remove duplicates from the conflict clause
     *
     * @return current conflict clause
     */
    Clause& finish();

    // get current unfinished conflict clause
    inline Clause& conflict() { return clause; }
    // get current unfinished conflict clause
    inline Clause const& conflict() const { return clause; }

private:
    Linear_arithmetic* lra;
    Clause clause;
};

/** Analysis of bound conflicts.
 */
class Bound_conflict_analysis {
public:
    using Models = Theory_models<Rational>;
    using Constraint = Linear_constraint<Rational>;
    using Polynomial = detail::Linear_polynomial<Rational>;

    inline Bound_conflict_analysis(Linear_arithmetic* lra) : lra(lra) {}

    /** Check if there is a bound conflict and provide an explanation if there is a conflict.
     *
     * @param trail current solver trail
     * @param bounds map rational variable -> implied bounds for that variable
     * @param var_ord checked rational variable
     * @return conflict clause if there is a bound conflict. None, otherwise.
     */
    std::optional<Clause> analyze(Trail& trail, Bounds& bounds, int var_ord);

private:
    Linear_arithmetic* lra;
};

/** Analysis of inequality conflicts.
 */
class Inequality_conflict_analysis {
public:
    using Models = Theory_models<Rational>;
    using Constraint = Linear_constraint<Rational>;
    using Polynomial = detail::Linear_polynomial<Rational>;

    inline Inequality_conflict_analysis(Linear_arithmetic* lra) : lra(lra), fm(lra) {}

    /** Check if there is an inequality conflict - i.e., `L <= x` and `x <= U` and `x != D`
     * where L, U, D evaluate to the same value in @p trail
     *
     * @param trail current solver trail
     * @param bounds map rational variable -> implied bounds for that variable
     * @param var_ord checked rational variable
     * @return conflict clause if there is an inequality conflict. None, otherwise.
     */
    std::optional<Clause> analyze(Trail& trail, Bounds& bounds, int var_ord);

private:
    Linear_arithmetic* lra;
    Fm_elimination fm;
};

} // namespace yaga

#endif // YAGA_LRA_CONFLICT_ANALYSIS_H