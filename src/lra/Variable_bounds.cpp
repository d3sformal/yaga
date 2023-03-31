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

void Variable_bounds::deduce_from_equality(Models const& models, Constraint cons)
{
    assert(!cons.lit().is_negation());
    assert(cons.pred() == Order_predicate::eq);
    assert(eval(models.boolean(), cons.lit()) == true);

    std::array<Deduced_properties, 2> props;
    props[0].bound = props[1].bound = cons.rhs();
    props[0].num_vars = props[1].num_vars = 0;

    auto [var_it, var_end] = cons.vars();
    auto coef_it = cons.coef().begin();
    for (; var_it != var_end; ++var_it, ++coef_it)
    {
        if (models.owned().is_defined(*var_it))
        {
            for (auto& prop : props)
            {
                prop.bound -= *coef_it * models.owned().value(*var_it);
            }
        }
        else // `*var_it` is unassigned
        {
            // bounds used to derive a lower/upper bound from this equality using FM elimination
            std::array<Bound const*, 2> var_bounds{
                bounds[*var_it].upper_bound(models),
                bounds[*var_it].lower_bound(models)
            };
            if (*coef_it < 0)
            {
                std::swap(var_bounds[0], var_bounds[1]);
            }

            // stop the computation if there is a circular dependency
            if ((var_bounds[0] && depends_on(*var_bounds[0], cons.lit().var().ord())) ||
                (var_bounds[1] && depends_on(*var_bounds[1], cons.lit().var().ord())))
            {
                return;
            }

            for (int i = 0; i < 2; ++i)
            {
                if (var_bounds[i])
                {
                    props[i].bound -= *coef_it * var_bounds[i]->value();
                    props[i].deps.push_back(*var_bounds[i]);
                }
                else
                {
                    ++props[i].num_vars;
                    props[i].unbounded_var = *var_it;
                    props[i].unbounded_coef = *coef_it;
                }
            }
        }
    }

    float max_deps = std::max<float>(threshold * cons.vars().size(), 0);
    int i = 0;
    for (auto& prop : props)
    {
        if (count_distinct_bounds(prop.deps) <= max_deps && prop.num_vars == 1)
        {
            prop.bound /= prop.unbounded_coef;

            bool has_changed = false;
            Bound value{prop.unbounded_var, prop.bound, cons, models, prop.deps};
            if ((i == 0 && prop.unbounded_coef > 0) || (i == 1 && prop.unbounded_coef < 0))
            {
                has_changed |= bounds[prop.unbounded_var].add_lower_bound(models, std::move(value));
            }
            else
            {
                has_changed |= bounds[prop.unbounded_var].add_upper_bound(models, std::move(value));
            }

            if (has_changed)
            {
                updated_write.push_back(prop.unbounded_var);
            }
        }
        ++i;
    }
}

void Variable_bounds::deduce_from_inequality(Models const& models, Constraint cons)
{
    assert(eval(models.boolean(), cons.lit()) == true);
    assert(cons.pred() != Order_predicate::eq);

    std::vector<Bound> deps;
    auto bound = cons.rhs();
    int num_unbounded = 0;
    int unbounded_var = 0;
    Rational unbounded_coef;
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
            Bound const* var_bound = nullptr;
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
            else
            {
                ++num_unbounded;
                unbounded_var = *var_it;
                unbounded_coef = *coef_it;
            }
        }
    }

    float max_deps = std::max<float>(threshold * cons.vars().size(), 0);
    if (count_distinct_bounds(deps) <= max_deps && num_unbounded == 1)
    {
        bound /= unbounded_coef;

        bool has_changed = false;
        Bound value{unbounded_var, bound, cons, models, deps};
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

void Variable_bounds::deduce(Models const& models, Constraint cons)
{
    assert(eval(models.boolean(), cons.lit()) == true);
    if (cons.size() <= 1)
    {
        return;
    }

    if (cons.pred() == Order_predicate::eq)
    {
        if (!cons.lit().is_negation())
        {
            deduce_from_equality(models, cons);
        }
        return;
    }
    else // inequality (<, <=, >, >=)
    {
        deduce_from_inequality(models, cons);
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