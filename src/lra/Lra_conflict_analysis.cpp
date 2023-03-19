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

bool Bound_conflict_analysis::in_conflict(Models const& models, Variable_bounds& bounds) const
{
    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
    if (!lb || !ub)
    {
        return false;
    }

    auto is_strict = lb->reason().is_strict() || ub->reason().is_strict();
    return lb->value() > ub->value() || (lb->value() == ub->value() && is_strict);
}

std::optional<Clause> Bound_conflict_analysis::analyze(Trail& trail, Variable_bounds& bounds)
{
    auto models = lra->relevant_models(trail);
    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
    if (!lb || !ub)
    {
        return {}; // no conflict
    }

    auto is_strict = lb->reason().is_strict() || ub->reason().is_strict();
    if (lb->value() < ub->value() || (lb->value() == ub->value() && !is_strict))
    {
        return {}; // no conflict
    }
    assert(lb->reason().vars().front() == ub->reason().vars().front());

    Clause conflict{lb->reason().lit().negate(), ub->reason().lit().negate()};
    fm.init(lb->reason());
    fm.resolve(ub->reason());
    //minimize(trail, conflict);
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

void Bound_conflict_analysis::minimize(Trail& trail, Clause& conflict)
{
    auto models = lra->relevant_models(trail);
    while (!fm.derived().empty())
    {
        // move the top level variable to the front
        auto top_it = fm.derived().begin();
        for (auto it = ++fm.derived().begin(); it != fm.derived().end(); ++it)
        {
            if (trail.decision_level(Variable{it->first, Variable::rational}).value() > trail.decision_level(Variable{top_it->first, Variable::rational}))
            {
                top_it = it;
            }
        }
        std::iter_swap(top_it, fm.derived().begin());

        // resolve bound conflict with the top level variable
        if (auto cons = find_conflict(models))
        {
            fm.resolve(cons.value());
            conflict.push_back(cons.value().lit().negate());
        }
        else
        {
            break;
        }
    }
}

std::optional<Bound_conflict_analysis::Constraint> Bound_conflict_analysis::find_conflict(Models const& models)
{
    auto [var_ord, var_coef] = *fm.derived().begin();
    auto& bounds = lra->find_bounds(var_ord);
    auto value = fm.derived().implied_value(models);
    if (var_coef < 0 || fm.predicate() == Order_predicate::eq) // `value` is a lower bound
    {
        if (auto ub = bounds.upper_bound(models))
        {
            auto is_strict = ub->reason().is_strict() || fm.predicate() == Order_predicate::lt;
            if (ub->value() < value || (ub->value() == value && is_strict))
            {
                return ub->reason();
            }
        }
    }

    if (var_coef > 0 || fm.predicate() == Order_predicate::eq) // `value` is an upper bound
    {
        if (auto lb = bounds.lower_bound(models))
        {
            auto is_strict = lb->reason().is_strict() || fm.predicate() == Order_predicate::lt;
            if (lb->value() > value || (lb->value() == value && is_strict))
            {
                return lb->reason();
            }
        }
    }

    return {};
}

bool Inequality_conflict_analysis::in_conflict(Models const& models, Variable_bounds& bounds) const
{
    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
    if (!lb || !ub)
    {
        return false;
    }

    if (lb->value() != ub->value() || lb->reason().is_strict() || ub->reason().is_strict())
    {
        return false;
    }

    // check if `x != D` where D, L, U evaluate to the same value
    return !!bounds.inequality(models, lb->value());
}

std::optional<Clause> Inequality_conflict_analysis::analyze(Trail& trail, Variable_bounds& bounds)
{
    auto models = lra->relevant_models(trail);
    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
    if (!lb || !ub)
    {
        return {}; // no conflict
    }

    // check if `L <= x` and `x <= U` and L, U evaluate to the same value where `x` is the
    // unassigned variable
    if (lb->value() != ub->value() || lb->reason().is_strict() || ub->reason().is_strict())
    {
        return {};
    }

    // check if `x != D` where D, L, U evaluate to the same value
    auto neq = bounds.inequality(models, lb->value());
    if (!neq)
    {
        return {};
    }
    assert(neq->reason().vars().front() == lb->reason().vars().front());
    assert(neq->reason().vars().front() == ub->reason().vars().front());

    Clause conflict{lb->reason().lit().negate(), ub->reason().lit().negate(),
                    neq->reason().lit().negate()};

    // special case where `x = E` and `x != D` where E, D evaluate to the same value
    if (lb->reason().lit() == ub->reason().lit())
    {
        // see: http://leodemoura.github.io/files/fmcad2013.pdf
        // We use `x = E && x != D -> E != D` as an explanation which is equivalent to 
        // the disequality lemma (Fig. 2) in this special case (we apply one final normalization
        // rule in the derivation in Fig. 2).
        assert(lb->reason().pred() == Order_predicate::eq);
        assert(!lb->reason().lit().is_negation());
        assert(lb->reason().vars().size() > 1 || neq->reason().vars().size() > 1);
        fm.init(neq->reason(), Order_predicate::eq, 1);
        fm.resolve(lb->reason());
        auto cons = fm.finish(trail);
        assert(!cons.empty());
        assert(eval(models.owned(), cons.negate()) == false);
        assert(eval(models.boolean(), cons.lit().negate()) == false);
        return Clause{lb->reason().lit().negate(), neq->reason().lit().negate(), 
                      cons.lit().negate()};
    }

    // if `L < D` may be non-trivial (i.e., it may contain at least one variable)
    if (lb->reason().vars().size() > 1 || neq->reason().vars().size() > 1)
    {
        // create and propagate `L < D` semantically
        auto mult = neq->reason().coef().front() > 0 ? 1 : -1;
        fm.init(neq->reason(), Order_predicate::lt, mult);
        fm.resolve(lb->reason());
        auto cons = fm.finish(trail);
        if (!cons.empty()) // `L < D` is non-trivial
        {
            assert(eval(models.owned(), cons) == false);
            assert(eval(models.boolean(), cons.lit()) == false);
            conflict.push_back(cons.lit());
        }
    }

    // if `D < U` may be non-trivial (i.e., it may contain at least one variable)
    if (ub->reason().vars().size() > 1 || neq->reason().vars().size() > 1)
    {
        // create and propagate `D < U` semantically
        auto mult = neq->reason().coef().front() > 0 ? -1 : 1;
        fm.init(neq->reason(), Order_predicate::lt, mult);
        fm.resolve(ub->reason());
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