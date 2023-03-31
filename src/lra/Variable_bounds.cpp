#include "Variable_bounds.h"

namespace perun {

void Variable_bounds::resize(int num_vars)
{
    bounds.resize(num_vars);
}

bool Variable_bounds::depends_on(Implied_value<Rational> const& bound, int bool_var) const
{
    return std::any_of(bound.bounds().begin(), bound.bounds().end(), [&](auto const& other) {
        return other.reason().lit().var().ord() == bool_var || depends_on(other, bool_var);
    });
}

void Variable_bounds::deduce(Models const& models, Constraint cons)
{
    assert(eval(models.boolean(), cons.lit()) == true);
    if (cons.pred() == Order_predicate::eq)
    {
        return;
    }

    auto bound = cons.rhs();
    int num_unbounded = 0;
    int unbounded_var = 0;
    Rational unbounded_coef{0};
    std::vector<Implied_value<Rational>> deps;

    auto [var_it, var_end] = cons.vars();
    auto coef_it = cons.coef().begin();
    for (; var_it != var_end; ++var_it, ++coef_it)
    {
        if (models.owned().is_defined(*var_it))
        {
            bound -= *coef_it * models.owned().value(*var_it);
        }
        else // `*var_it` is unassigned
        {
            // find appropriate bound for the variable
            Implied_value<Rational> const* var_bound = nullptr;
            if ((!cons.lit().is_negation() && *coef_it > 0) || 
                (cons.lit().is_negation() && *coef_it < 0))
            {
                var_bound = bounds[*var_it].lower_bound(models);
            }
            else
            {
                var_bound = bounds[*var_it].upper_bound(models);
            }

            if (var_bound && depends_on(*var_bound, cons.lit().var().ord()))
            {
                return;
            }

            if (var_bound)
            {
                bound -= *coef_it * var_bound->value();
                deps.push_back(*var_bound);
            }
            else // `*var_it` is not bounded
            {
                ++num_unbounded;
                unbounded_var = *var_it;
                unbounded_coef = *coef_it;
            }
        }
    }

    if (num_unbounded == 1)
    {
        bound /= unbounded_coef;

        bool has_changed = false;
        Implied_value<Rational> value{unbounded_var, bound, cons, models, deps};
        if ((!cons.lit().is_negation() && unbounded_coef > 0) ||
            (cons.lit().is_negation() && unbounded_coef < 0))
        {
            has_changed |= bounds[unbounded_var].add_upper_bound(models, std::move(value));
        }
        else
        {
            has_changed |= bounds[unbounded_var].add_lower_bound(models, std::move(value));
        }

        if (has_changed)
        {
            updated_write.push_back(unbounded_var);
        }
    }
}

bool Variable_bounds::is_implied(Models const& models, Constraint cons)
{
    auto val = eval(models.boolean(), cons.lit());
    if (val == true)
    {
        return true;
    }
    else if (val == false)
    {
        return false;
    }

    auto bound = cons.rhs();
    auto [var_it, var_end] = cons.vars();
    auto coef_it = cons.coef().begin();
    for (; var_it != var_end; ++var_it, ++coef_it)
    {
        if (models.owned().is_defined(*var_it))
        {
            bound -= *coef_it * models.owned().value(*var_it);
        }
        else
        {
            Implied_value<Rational> const* bound_ptr = nullptr;
            if ((!cons.lit().is_negation() && *coef_it > 0) ||
                (cons.lit().is_negation() && *coef_it < 0))
            {
                bound_ptr = bounds[*var_it].upper_bound(models);
            }
            else
            {
                bound_ptr = bounds[*var_it].lower_bound(models);
            }

            if (!bound_ptr)
            {
                return false;
            }
            bound -= *coef_it * bound_ptr->value();
        }
    }
    return cons.lit().is_negation() ? !cons.pred()(Rational{0}, bound) 
                                    : cons.pred()(Rational{0}, bound);
}

bool Variable_bounds::implies_equality(Constraint const& cons) const
{
    return cons.pred() == Order_predicate::eq && !cons.lit().is_negation();
}

bool Variable_bounds::implies_inequality(Constraint const& cons) const
{
    return cons.pred() == Order_predicate::eq && cons.lit().is_negation();
}

bool Variable_bounds::implies_lower_bound(Constraint const& cons) const
{
    if (cons.pred() == Order_predicate::eq)
    {
        return !cons.lit().is_negation();
    }

    return (cons.coef().front() > 0 && cons.lit().is_negation()) ||
           (cons.coef().front() < 0 && !cons.lit().is_negation());
}

bool Variable_bounds::implies_upper_bound(Constraint const& cons) const
{
    if (cons.pred() == Order_predicate::eq)
    {
        return !cons.lit().is_negation();
    }

    return (cons.coef().front() < 0 && cons.lit().is_negation()) ||
           (cons.coef().front() > 0 && !cons.lit().is_negation());
}

void Variable_bounds::update(Models const& models, Constraint cons)
{
    assert(models.boolean().is_defined(cons.lit().var().ord()));
    assert(cons.coef().front() != 0);

    auto value = cons.implied_value(models.owned()) / cons.coef().front();
    int var = cons.vars().front();

    // find which constraint is on the trail (either cons or its negation)
    cons = perun::eval(models.boolean(), cons.lit()).value() ? cons : cons.negate();

    bool has_changed = false;
    if (implies_equality(cons))
    {
        has_changed |= bounds[var].add_lower_bound(models, {var, value, cons, models});
        has_changed |= bounds[var].add_upper_bound(models, {var, value, cons, models});
    }
    else if (implies_inequality(cons))
    {
        has_changed = true;
        bounds[var].add_inequality({var, value, cons, models});
    }
    else if (implies_lower_bound(cons))
    {
        has_changed |= bounds[var].add_lower_bound(models, {var, value, cons, models});
    }
    else // upper bound
    {
        assert(implies_upper_bound(cons));
        has_changed |= bounds[var].add_upper_bound(models, {var, value, cons, models});
    }

    if (has_changed)
    {
        updated_write.push_back(var);
    }
}

std::vector<int> const& Variable_bounds::changed()
{
    std::swap(updated_read, updated_write);
    // remove duplicated in the read buffer
    std::sort(updated_read.begin(), updated_read.end());
    updated_read.erase(std::unique(updated_read.begin(), updated_read.end()), updated_read.end());
    // clear the write buffer
    updated_write.clear();
    return updated_read;
}

}