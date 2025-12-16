#include "Lra_conflict_analysis.h"
#include "Conflict_analysis.h"
#include "Linear_arithmetic.h"

#include <array>

namespace yaga {

namespace {

using Models = Theory_models<Rational>;
using Bound = Implied_value<Rational>;

Rational integer_lower_bound(Bound const& lb)
{
    auto result = lb.value().ceil();
    if (lb.is_strict() && lb.value().isInteger())
    {
        result += 1;
    }
    return result;
}

Rational integer_upper_bound(Bound const& ub)
{
    auto result = ub.value().floor();
    if (ub.is_strict() && ub.value().isInteger())
    {
        result -= 1;
    }
    return result;
}

void collect_assigned_vars(Fm_elimination const& fm, int excluded_var, std::vector<int>& out)
{
    for (auto const& [var, _] : fm.derived())
    {
        if (var != excluded_var)
        {
            out.push_back(var);
        }
    }
}

void add_assignment_literal(Linear_arithmetic* lra, Trail& trail, Models& models, Clause& out,
                            int var_ord)
{
    if (!models.owned().is_defined(var_ord))
    {
        return;
    }

    std::array<int, 1> vars{var_ord};
    std::array<Rational, 1> coef{Rational{1}};
    auto eq = lra->constraint(trail, vars, coef, Order_predicate::eq, models.owned().value(var_ord));

    // Make sure the equality is assigned in the boolean model.
    if (!models.boolean().is_defined(eq.lit().var().ord()))
    {
        lra->propagate(trail, models, eq);
    }

    assert(eval(models.owned(), eq) == true);
    assert(eval(models.boolean(), eq.lit()) == true);
    out.push_back(~eq.lit()); // add inequality: var != current_value
}

Clause compute_uip(Trail const& trail, Clause&& conflict)
{
    Conflict_analysis analysis;
    return analysis.analyze(trail, std::move(conflict)).first;
}

} // namespace

void Fm_elimination::init(Constraint const& cons)
{
    assert(cons.pred() != Order_predicate::eq || !cons.lit().is_negation()); // cons is not !=

    // Convert `cons` to an internal representation of a linear constraint:
    // `polynomial {<,<=,=} 0`. If `cons` is negated, its polynomial has to be multiplied
    // by -1 and we have to switch < to <= and <= to <.
    // For example, `not(x <= 0)` -> `x > 0` -> `-x < 0`.
    auto new_pred = cons.pred();
    if (cons.lit().is_negation())
    {
        if (new_pred == Order_predicate::leq)
        {
            new_pred = Order_predicate::lt;
        }
        else if (new_pred == Order_predicate::lt)
        {
            new_pred = Order_predicate::leq;
        }
    }
    init(cons, new_pred, new_pred != cons.pred() ? -1 : 1);
}

void Fm_elimination::init(Constraint const& cons, Order_predicate p, Rational mult)
{
    assert(!cons.empty());

    pred = p;
    poly.variables.clear();
    poly.variables.reserve(cons.vars().size());

    auto var_it = cons.vars().begin();
    auto coef_it = cons.coef().begin();
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        poly.variables.emplace_back(*var_it, *coef_it * mult);
    }
    poly.constant = -cons.rhs() * mult;
}

void Fm_elimination::init(Fm_elimination&& other)
{
    pred = other.pred;
    poly = std::move(other.poly);
}

void Fm_elimination::resolve(Fm_elimination const& other, int var_ord)
{
    assert(!poly.empty());
    assert(!other.derived().variables.empty());

    // find the variable to eliminate in `poly`
    auto poly_it = std::find_if(poly.begin(), poly.end(),
                                [var_ord](auto const& pair) { return pair.first == var_ord; });
    assert(poly_it != poly.end());

    // find the variable to eliminate in `other`
    auto other_it = std::find_if(other.derived().begin(), other.derived().end(),
                                 [var_ord](auto const& pair) { return pair.first == var_ord; });
    assert(other_it != other.derived().end());
    assert(other_it->first == poly_it->first);

    auto other_mult = -poly_it->second / other_it->second;
    if (other_mult < 0 && other.predicate() != Order_predicate::eq)
    {
        // predicate of the derived constraint would be > or >= if we used `other_mult`
        other_mult = -other_mult;
        // multiply `poly` by -1
        for (auto& [_, coef] : poly)
        {
            coef = -coef;
        }
        poly.constant = -poly.constant;
    }

    // eliminate `var_ord`
    for (auto [var, coef] : other.derived())
    {
        poly.variables.emplace_back(var, coef * other_mult);
    }
    poly.constant = poly.constant + other.derived().constant * other_mult;
    poly.normalize();

    assert(std::find_if(poly.begin(), poly.end(), [&](auto var) { return var.first == var_ord; }) ==
           poly.end());

    // find predicate of the derivation
    pred = combine(pred, other.predicate());
}

Order_predicate Fm_elimination::combine(Order_predicate first, Order_predicate second) const
{
    if (first == Order_predicate::eq && second == Order_predicate::eq)
    {
        return Order_predicate::eq;
    }
    else if (first != Order_predicate::lt && second != Order_predicate::lt)
    {
        return Order_predicate::leq;
    }
    else
    {
        return Order_predicate::lt;
    }
}

Fm_elimination::Constraint Fm_elimination::finish(Trail& trail)
{
    if (poly.empty())
    {
        return {};
    }

    // sort the polynomial by decision level
    std::sort(poly.begin(), poly.end(), [&](auto lhs, auto rhs) {
        Variable lhs_var{lhs.first, Variable::rational};
        Variable rhs_var{rhs.first, Variable::rational};
        return trail.decision_level(lhs_var).value() > trail.decision_level(rhs_var).value();
    });

    auto cons = lra->constraint(trail, std::views::keys(poly.variables),
                                std::views::values(poly.variables), pred, -poly.constant);
    auto models = lra->relevant_models(trail);
    if (!models.boolean().is_defined(cons.lit().var().ord()))
    {
        lra->propagate(trail, models, cons);
    }
    return cons;
}

Fm_elimination Lra_conflict_analysis::eliminate(Models const& models, Bounds& bounds,
                                                Implied_value<Rational> const& bound)
{
    // add assumption to the implication
    clause.push_back(~bound.reason().lit());

    // eliminate all unassigned variables in the linear constraint except for `bound.var()`
    Fm_elimination fm{lra, bound.reason()};
    for (auto const& other : bound.bounds())
    {
        if (!models.owned().is_defined(other.var()))
        {
            fm.resolve(eliminate(models, bounds, other), other.var());
        }
    }
    return fm;
}

Clause& Lra_conflict_analysis::finish()
{
    // remove duplicate literals from the conflict clause
    std::sort(conflict().begin(), conflict().end(), Literal_comparer{});
    conflict().erase(std::unique(conflict().begin(), conflict().end()), conflict().end());
    return clause;
}

std::optional<Clause> Bound_conflict_analysis::analyze(Trail& trail, Bounds& bounds, int var_ord) {
    auto models = lra->relevant_models(trail);
    auto lb = bounds[var_ord].lower_bound(models);
    auto ub = bounds[var_ord].upper_bound(models);
    if (!lb || !ub)
    {
        return {}; // no conflict
    }

    auto is_strict = lb->is_strict() || ub->is_strict();
    if (!lia)
    {
        if (lb->value() < ub->value() || (lb->value() == ub->value() && !is_strict))
        {
            return {}; // no conflict
        }
        assert(lb->var() == ub->var());

        // Derive a conflict using FM elimination. We implicitly use resolution to resolve intermediate
        // results.
        Lra_conflict_analysis analysis{lra, lia};
        auto fm = analysis.eliminate(models, bounds, *lb);
        fm.resolve(analysis.eliminate(models, bounds, *ub), ub->var());

        auto& conflict = analysis.finish();
        auto derived = fm.finish(trail);
        if (!derived.empty())
        {
            assert(eval(models.boolean(), derived.lit()) == false);
            assert(eval(models.owned(), derived) == false);
            conflict.push_back(derived.lit());
        }

        assert(conflict.size() >= 2);
        assert(eval(models.boolean(), conflict) == false);
        return conflict;
    }
    else  // lia
    {
        auto const lb_int = integer_lower_bound(*lb);
        auto const ub_int = integer_upper_bound(*ub);
        if (lb_int <= ub_int)
        {
            return {}; // there is an integer value between the bounds
        }

        // Explain the conflict by collecting constraint assumptions and equalities of all
        // assigned variables that were used to derive the conflicting bounds.
        Lra_conflict_analysis analysis{lra, lia};
        auto fm_lb = analysis.eliminate(models, bounds, *lb);
        auto fm_ub = analysis.eliminate(models, bounds, *ub);

        std::vector<int> assigned_vars;
        assigned_vars.reserve(static_cast<std::size_t>(fm_lb.derived().size() + fm_ub.derived().size()));
        collect_assigned_vars(fm_lb, var_ord, assigned_vars);
        collect_assigned_vars(fm_ub, var_ord, assigned_vars);
        std::sort(assigned_vars.begin(), assigned_vars.end());
        assigned_vars.erase(std::unique(assigned_vars.begin(), assigned_vars.end()), assigned_vars.end());

        for (auto assigned_var : assigned_vars)
        {
            add_assignment_literal(lra, trail, models, analysis.conflict(), assigned_var);
        }

        auto clause = analysis.finish();
        assert(!clause.empty());
        assert(eval(models.boolean(), clause) == false);
        return compute_uip(trail, std::move(clause));
    }

}

std::optional<Clause> Inequality_conflict_analysis::analyze(Trail& trail, Bounds& bounds,
                                                            int var_ord)
{
    auto models = lra->relevant_models(trail);
    auto lb = bounds[var_ord].lower_bound(models);
    auto ub = bounds[var_ord].upper_bound(models);
    if (!lb || !ub)
    {
        return {}; // no conflict
    }

    if (!lia) {
        // check if `L <= x` and `x <= U` and L, U evaluate to the same value where `x` is the
        // check, unassigned variable
        if (lb->value() != ub->value() || lb->reason().is_strict() || ub->reason().is_strict())
        {
            return {};
        }

        // check if `x != D` where D, L, U evaluate to the same value
        auto neq = bounds[var_ord].inequality(models, lb->value());
        if (!neq)
        {
            return {};
        }
        assert(lb->var() == ub->var());
        assert(neq->var() == lb->var());

        Lra_conflict_analysis analysis{lra, lia};
        analysis.conflict().push_back(~neq->reason().lit());

        auto mult = neq->reason().coef().front() > 0 ? 1 : -1;
        for (auto bound_ptr : {lb, ub})
        {
            auto fm = analysis.eliminate(models, bounds, *bound_ptr);
            fm.resolve(Fm_elimination{lra, neq->reason(), Order_predicate::lt, mult}, neq->var());
            auto derived = fm.finish(trail);
            if (!derived.empty())
            {
                assert(eval(models.owned(), derived) == false);
                assert(eval(models.boolean(), derived.lit()) == false);
                analysis.conflict().push_back(derived.lit());
            }
            mult = -mult;
        }

        assert(eval(models.boolean(), analysis.conflict()) == false);
        return analysis.finish();
    } else {  // lia
        auto const lb_int = integer_lower_bound(*lb);
        auto const ub_int = integer_upper_bound(*ub);

        if (lb_int > ub_int)
        {
            return {}; // bound conflict (handled by Bound_conflict_analysis)
        }
        if (lb_int != ub_int)
        {
            return {}; // there is an integer value different from the disallowed one
        }

        auto const& value = lb_int; // the only integer value allowed by the bounds
        auto neq = bounds[var_ord].inequality(models, value);
        if (!neq)
        {
            return {};
        }
        assert(lb->var() == ub->var());
        assert(neq->var() == lb->var());

        Lra_conflict_analysis analysis{lra, lia};
        analysis.conflict().push_back(~neq->reason().lit()); // add equality: x == value

        auto fm_lb = analysis.eliminate(models, bounds, *lb);
        auto fm_ub = analysis.eliminate(models, bounds, *ub);

        std::vector<int> assigned_vars;
        assigned_vars.reserve(static_cast<std::size_t>(fm_lb.derived().size() + fm_ub.derived().size() +
                                                       neq->reason().size()));
        collect_assigned_vars(fm_lb, var_ord, assigned_vars);
        collect_assigned_vars(fm_ub, var_ord, assigned_vars);
        for (auto other_var : neq->reason().vars())
        {
            if (other_var != var_ord && models.owned().is_defined(other_var))
            {
                assigned_vars.push_back(other_var);
            }
        }
        std::sort(assigned_vars.begin(), assigned_vars.end());
        assigned_vars.erase(std::unique(assigned_vars.begin(), assigned_vars.end()), assigned_vars.end());

        for (auto assigned_var : assigned_vars)
        {
            add_assignment_literal(lra, trail, models, analysis.conflict(), assigned_var);
        }

        auto clause = analysis.finish();
        assert(!clause.empty());
        assert(eval(models.boolean(), clause) == false);
        return compute_uip(trail, std::move(clause));
    }
}

} // namespace yaga
