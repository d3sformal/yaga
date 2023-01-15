#ifndef PREUN_LINEAR_CONSTRAINTS_H
#define PREUN_LINEAR_CONSTRAINTS_H

#include <algorithm>
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
#include "Linear_constraint.h"
#include "Model.h"
#include "Variable.h"

namespace perun {

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
     * The constraint is normalized. The returned constraint might represent negation of some 
     * preexisting constraint in which case, literal of the returned constraint will be negated.
     *
     * @param var_range ordinal numbers of variables in the constraint
     * @param coef_range coefficients of variables in the constraint
     * @param pred predicate of the constraint
     * @param rhs constant on the right-hand-side of the constraint
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

    /** Find boolean constraint which implements @p bool_var_ord
     *
     * @param bool_var_ord ordinal number of a boolean variable
     * @return constraint which implements @p bool_var_ord or an empty constraint, if there is no
     * linear constraint for @p bool_var_ord
     */
    Constraint_type operator[](int bool_var_ord) const
    {
        if (bool_var_ord < 0 || bool_var_ord >= static_cast<int>(constraints.size()))
        {
            return {}; // empty constraint
        }
        return constraints[bool_var_ord];
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
        auto rhs = cons.rhs();
        auto [var_it, var_end] = vars(cons);
        auto [coef_it, coef_end] = coef(cons);
        for (; var_it != var_end; ++var_it, ++coef_it)
        {
            assert(coef_it != coef_end);
            assert(model.is_defined(*var_it));
            rhs -= *coef_it * model.value(*var_it);
        }
        return cons.lit().is_negation() ^ cons.pred()(Value_type{0}, rhs);
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