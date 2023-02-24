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

void Fourier_motzkin_elimination::resolve(Constraint const& cons)
{
    assert(!poly.empty());
    assert(!cons.empty());
    assert(cons.pred() != Order_predicate::eq || !cons.lit().is_negation()); // cons is not !=

    // find the variable to eliminate in `poly`
    auto poly_it = poly.begin();

    // find the variable to eliminate in `cons`
    auto cons_var_it = std::find(cons.vars().begin(), cons.vars().end(), poly_it->first);
    auto cons_coef_it = cons.coef().begin() + std::distance(cons.vars().begin(), cons_var_it);
    assert(cons_var_it != cons.vars().end());
    assert(cons_coef_it != cons.coef().end());
    assert(*cons_var_it == poly_it->first);
    assert(
        (is_lower_bound() &&
         is_upper_bound(*cons_coef_it, cons.pred(), cons.lit().is_negation())) ||
        (is_upper_bound() && is_lower_bound(*cons_coef_it, cons.pred(), cons.lit().is_negation())));

    // compute constants s.t. `poly + cons_mult * cons` eliminates the first variable in `poly`
    auto cons_mult = -poly_it->second / *cons_coef_it;
    auto cons_mult_signbit = cons_mult < 0;
    if (cons.pred() != Order_predicate::eq && cons_mult_signbit != cons.lit().is_negation())
    {
        // predicate of the derived constraint would be > or >= if we used `cons_mult`
        cons_mult = -cons_mult;
        // multiply `poly` by -1
        for (auto& [_, coef] : poly)
        {
            coef = -coef;
        }
        poly.constant = -poly.constant;
    }

    // multiply-add the polynomial of constraint `cons`
    auto var_it = cons.vars().begin();
    auto coef_it = cons.coef().begin();
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        poly.variables.emplace_back(*var_it, *coef_it * cons_mult);
    }
    poly.constant = poly.constant - cons.rhs() * cons_mult;
    poly.normalize();

    assert(std::find_if(poly.begin(), poly.end(),
                        [&](auto var) { return var.first == *cons_var_it; }) == poly.end());

    // find predicate of the derivation
    if (pred == Order_predicate::eq && cons.pred() == Order_predicate::eq)
    {
        pred = Order_predicate::eq;
    }
    else if (pred != Order_predicate::lt && !cons.is_strict())
    {
        pred = Order_predicate::leq;
    }
    else
    {
        pred = Order_predicate::lt;
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

std::optional<Clause> Bound_conflict_analysis::analyze(Trail& trail, Variable_bounds& bounds)
{
    auto models = lra->relevant_models(trail);
    auto lower_bound = bounds.lower_bound(models);
    auto upper_bound = bounds.upper_bound(models);
    if (!lower_bound || !upper_bound)
    {
        return {}; // no conflict
    }

    auto lb = lower_bound.value(); // L
    auto ub = upper_bound.value(); // U
    auto is_strict = lb.reason().is_strict() || ub.reason().is_strict();
    if (lb.value() < ub.value() || (lb.value() == ub.value() && !is_strict))
    {
        return {}; // no conflict
    }
    assert(lb.reason().vars().front() == ub.reason().vars().front());

    Clause conflict{lb.reason().lit().negate(), ub.reason().lit().negate()};
    fm.init(lb.reason());
    fm.resolve(ub.reason());
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

std::optional<Clause> Inequality_conflict_analysis::analyze(Trail& trail, Variable_bounds& bounds)
{
    auto models = lra->relevant_models(trail);
    auto lower_bound = bounds.lower_bound(models);
    auto upper_bound = bounds.upper_bound(models);
    if (!lower_bound || !upper_bound)
    {
        return {}; // no conflict
    }

    // check if `L <= x` and `x <= U` and L, U evaluate to the same value where `x` is the
    // unassigned variable
    auto lb = lower_bound.value(); // L
    auto ub = upper_bound.value(); // U
    if (lb.value() != ub.value() || lb.reason().is_strict() || ub.reason().is_strict())
    {
        return {};
    }

    // check if `x != D` where D, L, U evaluate to the same value
    auto inequality = bounds.inequality(models, lb.value());
    if (!inequality)
    {
        return {};
    }
    auto neq = inequality.value();
    assert(neq.reason().vars().front() == lb.reason().vars().front());
    assert(neq.reason().vars().front() == ub.reason().vars().front());

    Clause conflict{lb.reason().lit().negate(), ub.reason().lit().negate(),
                    neq.reason().lit().negate()};

    // if `L < D` may be non-trivial (i.e., it may contain at least one variable)
    if (lb.reason().vars().size() > 1 || neq.reason().vars().size() > 1)
    {
        // create and propagate `L < D` semantically
        auto mult = neq.reason().coef().front() > 0 ? 1 : -1;
        fm.init(neq.reason(), Order_predicate::lt, mult);
        fm.resolve(lb.reason());
        auto cons = fm.finish(trail);
        if (!cons.empty()) // `L < D` is non-trivial
        {
            assert(eval(models.owned(), cons) == false);
            assert(eval(models.boolean(), cons.lit()) == false);
            conflict.push_back(cons.lit());
        }
    }

    // if `D < U` may be non-trivial (i.e., it may contain at least one variable)
    if (ub.reason().vars().size() > 1 || neq.reason().vars().size() > 1)
    {
        // create and propagate `D < U` semantically
        auto mult = neq.reason().coef().front() > 0 ? -1 : 1;
        fm.init(neq.reason(), Order_predicate::lt, mult);
        fm.resolve(ub.reason());
        auto cons = fm.finish(trail);
        if (!cons.empty()) // `D < U` is non-trivial
        {
            assert(eval(models.owned(), cons) == false);
            assert(eval(models.boolean(), cons.lit()) == false);
            conflict.push_back(cons.lit());
        }
    }

    return conflict;
}

} // namespace perun