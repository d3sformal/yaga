#include "Arithmetic_conflict_analysis.h"
#include "Linear_arithmetic.h"

namespace perun {

void Fourier_motzkin_elimination::init_lower_bound(Constraint const& lb)
{
    assert(!lb.empty());
    // lb implies a lower bound
    assert(lb.coef().front() < 0 || lb.lit().is_negation() || lb.pred() == Order_predicate::eq);

    poly.variables.clear();

    auto mult = lb.coef().front() > 0 ? Rational{-1} : Rational{1};
    auto var_it = lb.vars().begin();
    auto coef_it = lb.coef().begin();
    for (; var_it != lb.vars().end(); ++var_it, ++coef_it)
    {
        poly.variables.emplace_back(*var_it, *coef_it * mult);
    }
    poly.constant = -lb.rhs() * mult;

    pred = lb.pred();
    if (lb.lit().is_negation())
    {
        // After we negate the constraint and multiply by -1, the inequality will change from
        // strict to non-strict or from non-strict to strict.
        // For example: `not(x < 1)` -> `x >= 1` -> `-x <= -1`
        assert(mult < 0 || pred == Order_predicate::eq);
        if (pred == Order_predicate::leq)
        {
            pred = Order_predicate::lt;
        }
        else if (pred == Order_predicate::lt)
        {
            pred = Order_predicate::leq;
        }
        else // if (pred == Order_predicate::eq)
        {
            // We have a constraint of type `x != D` which implies `x < D` or `x > D`. Given the
            // assumption that `lb` implies a lower bound, we assume `x > D`.
            pred = Order_predicate::lt;
        }
    }
}

void Fourier_motzkin_elimination::resolve(Constraint const& cons)
{
    assert(!poly.empty());
    assert(!cons.empty());

    // find the variable to eliminate in `poly`
    auto poly_it = poly.begin();

    // find the variable to eliminate in `cons`
    auto cons_var_it = std::find(cons.vars().begin(), cons.vars().end(), poly_it->first);
    auto cons_coef_it = cons.coef().begin() + std::distance(cons.vars().begin(), cons_var_it);
    assert(cons_var_it != cons.vars().end());
    assert(cons_coef_it != cons.coef().end());
    assert(*cons_var_it == poly_it->first);

    // compute constant s.t. `poly + mult * cons` eliminates the first variable in `poly`
    auto mult = -poly_it->second / *cons_coef_it;
    assert(mult > 0 || cons.lit().is_negation() || cons.pred() == Order_predicate::eq);

    // multiply-add the polynomial of constraint `cons`
    auto var_it = cons.vars().begin();
    auto coef_it = cons.coef().begin();
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        poly.variables.emplace_back(*var_it, *coef_it * mult);
    }
    poly.constant = poly.constant - cons.rhs() * mult;
    poly.normalize();

    assert(std::find_if(poly.begin(), poly.end(),
                        [&](auto var) { return var.first == *cons_var_it; }) == poly.end());

    // find predicate of the derivation
    if (pred == Order_predicate::eq && cons.pred() == Order_predicate::eq &&
        !cons.lit().is_negation())
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

    Clause conflict{lb.reason().lit().negate(), ub.reason().lit().negate()};
    fm.init_lower_bound(lb.reason());
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

    // check if `L <= x && x <= U` and `L = U` where `x` is the unassigned variable
    auto lb = lower_bound.value(); // L
    auto ub = upper_bound.value(); // U
    if (lb.value() != ub.value() || lb.reason().is_strict() || ub.reason().is_strict())
    {
        return {};
    }

    // check if `x != D` where `D = L`
    auto inequality = bounds.inequality(models, lb.value());
    if (!inequality)
    {
        return {};
    }

    Clause conflict{lb.reason().lit().negate(), ub.reason().lit().negate(),
                    inequality.value().reason().lit().negate()};

    // if `L < D` may be non-trivial (i.e., it contains at least one variable)
    if (lb.reason().vars().size() > 1 || inequality.value().reason().vars().size() > 1)
    {
        // create and propagate `L < D` semantically
        fm.init_lower_bound(lb.reason());
        fm.resolve(inequality.value().reason());
        auto cons = fm.finish(trail);
        if (!cons.empty())
        {
            assert(eval(models.owned(), cons) == false);
            assert(eval(models.boolean(), cons.lit()) == false);
            conflict.push_back(cons.lit());
        }
    }

    // if `D < U` is non-trivial (i.e., it contains at least one variable)
    if (ub.reason().vars().size() > 1 || inequality.value().reason().vars().size() > 1)
    {
        // create and propagate `D < U` semantically
        fm.init_lower_bound(inequality.value().reason());
        fm.resolve(ub.reason());
        auto cons = fm.finish(trail);
        if (!cons.empty())
        {
            assert(eval(models.owned(), cons) == false);
            assert(eval(models.boolean(), cons.lit()) == false);
            conflict.push_back(cons.lit());
        }
    }

    return conflict;
}

} // namespace perun