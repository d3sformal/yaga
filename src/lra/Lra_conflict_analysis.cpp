#include "Lra_conflict_analysis.h"
#include "Linear_arithmetic.h"

namespace perun {

void Fourier_motzkin_elimination::init(Constraint const& cons)
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

void Fourier_motzkin_elimination::init(Constraint const& cons, Order_predicate p, Rational mult)
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

void Fourier_motzkin_elimination::init(Fourier_motzkin_elimination&& other)
{
    pred = other.pred;
    poly = std::move(other.poly);
}

void Fourier_motzkin_elimination::resolve(Fourier_motzkin_elimination const& other, int var_ord)
{
    assert(!poly.empty());
    assert(!other.derived().variables.empty());

    // find the variable to eliminate in `poly`
    auto poly_it = std::find_if(poly.begin(), poly.end(), [var_ord](auto const& pair) {
        return pair.first == var_ord;
    });
    assert(poly_it != poly.end());

    // find the variable to eliminate in `other`
    auto other_it = std::find_if(other.derived().begin(), other.derived().end(), [var_ord](auto const& pair) {
        return pair.first == var_ord;
    });
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

    assert(std::find_if(poly.begin(), poly.end(),
                        [&](auto var) { return var.first == var_ord; }) == poly.end());

    // find predicate of the derivation
    pred = combine(pred, other.predicate());
}

Order_predicate Fourier_motzkin_elimination::combine(Order_predicate first, Order_predicate second) const
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

Fourier_motzkin_elimination::Constraint Fourier_motzkin_elimination::finish(Trail& trail)
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

Fourier_motzkin_elimination Lra_conflict_analysis::eliminate(Models const& models, Variable_bounds& bounds, Implied_value<Rational> const& bound)
{
    // add assumption to the implication
    clause.push_back(bound.reason().lit().negate());

    // eliminate all unassigned variables in the linear constraint except for `bound.var()`
    Fourier_motzkin_elimination fm{lra, bound.reason()};
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

std::optional<Clause> Bound_conflict_analysis::analyze(Trail& trail, Variable_bounds& bounds, int var_ord)
{
    auto models = lra->relevant_models(trail);
    auto lb = bounds[var_ord].lower_bound(models);
    auto ub = bounds[var_ord].upper_bound(models);
    if (!lb || !ub)
    {
        return {}; // no conflict
    }

    auto is_strict = lb->is_strict() || ub->is_strict();
    if (lb->value() < ub->value() || (lb->value() == ub->value() && !is_strict))
    {
        return {}; // no conflict
    }
    assert(lb->var() == ub->var());

    // Derive a conflict using FM elimination. We implicitly use resolution to resolve intermediate 
    // results.
    Lra_conflict_analysis analysis{lra};
    auto fm = analysis.eliminate(models, bounds, *lb);
    fm.resolve(analysis.eliminate(models, bounds, *ub), ub->var());
    //fm = analysis.minimize(trail, models, bounds, std::move(fm));

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

std::optional<Clause> Inequality_conflict_analysis::analyze(Trail& trail, Variable_bounds& bounds, int var_ord)
{
    auto models = lra->relevant_models(trail);
    auto lb = bounds[var_ord].lower_bound(models);
    auto ub = bounds[var_ord].upper_bound(models);
    if (!lb || !ub)
    {
        return {}; // no conflict
    }

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

    Lra_conflict_analysis analysis{lra};
    analysis.conflict().push_back(neq->reason().lit().negate());

    auto mult = neq->reason().coef().front() > 0 ? 1 : -1;
    for (auto bound_ptr : {lb, ub})
    {
        auto fm = analysis.eliminate(models, bounds, *bound_ptr);
        fm.resolve(Fourier_motzkin_elimination{lra, neq->reason(), Order_predicate::lt, mult}, neq->var());
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
}

} // namespace perun