#include "Linear_arithmetic.h"

namespace perun {

void Linear_arithmetic::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::rational)
    {
        bounds.resize(num_vars);
        watched.resize(num_vars);
        cached_values.resize(num_vars);
    }
    else if (type == Variable::boolean)
    {
        constraints.resize(num_vars);
    }
}

void Linear_arithmetic::on_learned_clause(Database&, Trail& trail, Clause const&)
{
    cached_values = relevant_models(trail).owned();
}

std::optional<Clause> Linear_arithmetic::propagate(Database&, Trail& trail)
{
    auto models = relevant_models(trail);

    // find relevant variables which have been assigned at current decision level
    std::vector<Variable> variables;
    for (auto [var, _] : assigned(trail))
    {
        if (var.type() == Variable::rational ||
            (var.type() == Variable::boolean && !constraints[var.ord()].empty()))
        {
            variables.push_back(var);
        }
    }

    for (auto var : variables)
    {
        if (var.type() == Variable::boolean)
        {
            auto cons = constraints[var.ord()];
            assert(!cons.empty());
            if (models.owned().is_defined(cons.vars().front()))
            {
                assert(eval(models.owned(), cons) == eval(models.boolean(), cons.lit()));
            }
            else if (is_unit(models.owned(), cons))
            {
                if (auto conflict = unit(trail, models, cons))
                {
                    return conflict;
                }
            }
        }
        else if (var.type() == Variable::rational)
        {
            if (auto conflict = replace_watch(trail, models, var.ord()))
            {
                return conflict;
            }
        }
        else
        {
            assert(false);
        }
    }
    return {}; // no conflict
}

void Linear_arithmetic::watch(Constraint& cons)
{
    assert(!cons.empty());

    watched[cons.vars()[0]].push_back(cons);
    if (cons.size() > 1)
    {
        watched[cons.vars()[1]].push_back(cons);
    }
}

void Linear_arithmetic::watch(Constraint& cons, Model<Rational> const& model)
{
    // move 2 unassigned variables to the front
    auto out_var_it = cons.vars().begin();
    auto out_var_end = cons.size() == 1 ? out_var_it + 1 : out_var_it + 2;
    auto out_coef_it = cons.vars().begin();
    auto var_it = out_var_it;
    auto coef_it = out_coef_it;
    for (; var_it != cons.vars().end() && out_var_it != out_var_end; ++var_it, ++coef_it)
    {
        if (!model.is_defined(*var_it))
        {
            std::iter_swap(var_it, out_var_it++);
            std::iter_swap(coef_it, out_coef_it++);
        }
    }

    watch(cons);
}

bool Linear_arithmetic::replace_watch(Model<Rational> const& lra_model, Watched_constraint& watch,
                                      int lra_var_ord)
{
    auto& cons = watch.constraint;

    if (cons.size() <= 1)
    {
        assert(cons.vars().front() == lra_var_ord);
        return false;
    }

    // if both watched variables are assigned, the constraint is fully assigned
    if (lra_model.is_defined(cons.vars()[0]) && lra_model.is_defined(cons.vars()[1]))
    {
        assert(std::all_of(cons.vars().begin(), cons.vars().end(),
                           [&](auto var) { return lra_model.is_defined(var); }));
        return false;
    }

    // move the assigned variable to the second position
    auto rep_var_it = ++cons.vars().begin();
    auto rep_coef_it = ++cons.coef().begin();
    if (*rep_var_it != lra_var_ord)
    {
        std::iter_swap(cons.vars().begin(), rep_var_it);
        std::iter_swap(cons.coef().begin(), rep_coef_it);
    }
    assert(*rep_var_it == lra_var_ord);

    // find an unassigned variable to watch
    if (cons.size() > 2)
    {
        assert(2 <= watch.index && watch.index < cons.size());
        auto var_it = cons.vars().begin() + watch.index;
        auto coef_it = cons.coef().begin() + watch.index;
        auto const end_var_it = var_it;
        do
        {
            assert(coef_it != cons.coef().end());
            if (!lra_model.is_defined(*var_it))
            {
                std::iter_swap(rep_var_it, var_it);
                std::iter_swap(rep_coef_it, coef_it);
                watched[*rep_var_it].push_back(watch);
                break;
            }

            // move to the next variable
            ++watch.index;
            ++coef_it;
            if (++var_it == cons.vars().end())
            {
                var_it = cons.vars().begin() + 2; // skip the watched variables
                coef_it = cons.coef().begin() + 2;
                watch.index = 2;
            }
        } while (var_it != end_var_it);
    }

    return *rep_var_it != lra_var_ord;
}

std::optional<Clause> Linear_arithmetic::replace_watch(Trail& trail, Models& models,
                                                       int lra_var_ord)
{
    assert(models.owned().is_defined(lra_var_ord));

    auto& watchlist = watched[lra_var_ord];
    for (std::size_t i = 0; i < watchlist.size();)
    {
        auto& watch = watchlist[i];
        auto& cons = watch.constraint;

        if (replace_watch(models.owned(), watch, lra_var_ord))
        {
            // remove the watch
            std::swap(watchlist[i], watchlist.back());
            watchlist.pop_back();
        }
        else // cons is unit or fully assigned
        {
            if (models.boolean().is_defined(cons.lit().var().ord())) // cons is on the trail
            {
                if (models.owned().is_defined(cons.vars().front())) // cons is fully assigned
                {
                    assert(eval(models.owned(), cons) == eval(models.boolean(), cons.lit()));
                }
                else if (auto conflict = unit(trail, models, cons))
                {
                    return conflict;
                }
            }
            else // cons is *not* on the trail
            {
                if (models.owned().is_defined(cons.vars().front())) // cons is fully assigned
                {
                    propagate(trail, models, cons);
                }
            }
            ++i;
        }
    }
    return {}; // no conflict
}

void Linear_arithmetic::update_bounds(Models const& models, Constraint& cons)
{
    assert(!cons.empty());
    assert(!models.owned().is_defined(cons.vars().front()));
    assert(models.boolean().is_defined(cons.lit().var().ord()));
    assert(cons.coef().front() != 0);

    auto value = cons.implied_value(models.owned()) / cons.coef().front();
    // find constraint which should be true in current model (according to bool model)
    auto actual_cons = perun::eval(models.boolean(), cons.lit()).value() ? cons : cons.negate();

    if (implies_equality(actual_cons))
    {
        bounds[cons.vars().front()].add_lower_bound(models, {value, actual_cons, models});
        bounds[cons.vars().front()].add_upper_bound(models, {value, actual_cons, models});
    }
    else if (implies_inequality(actual_cons))
    {
        bounds[cons.vars().front()].add_inequality({value, actual_cons, models});
    }
    else if (implies_lower_bound(actual_cons))
    {
        bounds[cons.vars().front()].add_lower_bound(models, {value, actual_cons, models});
    }
    else // upper bound
    {
        assert(implies_upper_bound(actual_cons));
        bounds[cons.vars().front()].add_upper_bound(models, {value, actual_cons, models});
    }
}

bool Linear_arithmetic::implies_equality(Constraint const& cons) const
{
    return cons.pred() == Order_predicate::eq && !cons.lit().is_negation();
}

bool Linear_arithmetic::implies_inequality(Constraint const& cons) const
{
    return cons.pred() == Order_predicate::eq && cons.lit().is_negation();
}

bool Linear_arithmetic::implies_lower_bound(Constraint const& cons) const
{
    if (cons.pred() == Order_predicate::eq)
    {
        return true;
    }

    return (cons.coef().front() > 0 && cons.lit().is_negation()) ||
           (cons.coef().front() < 0 && !cons.lit().is_negation());
}

bool Linear_arithmetic::implies_upper_bound(Constraint const& cons) const
{
    if (cons.pred() == Order_predicate::eq)
    {
        return true;
    }

    return (cons.coef().front() < 0 && cons.lit().is_negation()) ||
           (cons.coef().front() > 0 && !cons.lit().is_negation());
}

std::optional<Clause> Linear_arithmetic::check_bounds(Trail& trail, Variable_bounds& bounds)
{
    if (auto conflict = Bound_conflict_analysis{this}.analyze(trail, bounds))
    {
        return conflict;
    }

    if (auto conflict = Inequality_conflict_analysis{this}.analyze(trail, bounds))
    {
        return conflict;
    }
    return {}; // no conflict
}

std::optional<Clause> Linear_arithmetic::unit(Trail& trail, Models& models, Constraint& cons)
{
    update_bounds(models, cons);
    if (auto conflict = check_bounds(trail, bounds[cons.vars().front()]))
    {
        return conflict;
    }
    return {};
}

void Linear_arithmetic::propagate(Trail& trail, Models& models, Constraint const& cons)
{
    assert(!eval(models.boolean(), cons.lit()));

    // find decision level of the propagation
    int dec_level = 0;
    for (auto var_ord : cons.vars())
    {
        auto level = trail.decision_level(Variable{var_ord, Variable::rational});
        assert(level.has_value());
        dec_level = std::max<int>(dec_level, level.value());
    }

    // propagate the boolean variable of the constraint
    auto value = cons.eval(models.owned());
    models.boolean().set_value(cons.lit().var().ord(), cons.lit().is_negation() ^ value);
    trail.propagate(cons.lit().var(), /*reason=*/nullptr, dec_level);
}

bool Linear_arithmetic::is_new(Models const& models, Variable var) const
{
    return (var.type() == Variable::boolean &&
            var.ord() >= static_cast<int>(models.boolean().num_vars())) ||
           (var.type() == Variable::rational &&
            var.ord() >= static_cast<int>(models.owned().num_vars()));
}

void Linear_arithmetic::add_variable(Trail& trail, Models const& models, Variable var)
{
    if (is_new(models, var))
    {
        trail.resize(var.type(), var.ord() + 1);
    }
}

std::optional<Linear_arithmetic::Rational> Linear_arithmetic::find_integer(Models const& models,
                                                                           Variable_bounds& bounds)
{
    auto abs = [](int val) -> int {
        if (val == std::numeric_limits<int>::min())
        {
            return std::numeric_limits<int>::max();
        }
        return val >= 0 ? val : -val;
    };

    Rational lb{std::numeric_limits<int>::lowest()};
    Rational ub{std::numeric_limits<int>::max()};
    if (auto lower_bound = bounds.lower_bound(models))
    {
        lb = lower_bound.value().value();
    }

    if (auto upper_bound = bounds.upper_bound(models))
    {
        ub = upper_bound.value().value();
    }

    int abs_min_value = 0;
    int abs_bound = 0;
    if (lb <= Rational{0} && ub >= Rational{0})
    {
        abs_bound = std::max<int>(abs(static_cast<int>(lb)), static_cast<int>(ub));
    }
    else if (lb > Rational{0})
    {
        abs_min_value = static_cast<int>(lb);
        abs_bound = static_cast<int>(ub);
    }
    else // lb <= ub < 0
    {
        abs_bound = abs(static_cast<int>(lb));
        abs_min_value = abs(static_cast<int>(ub));
    }
    assert(abs_bound >= 0);
    assert(abs_min_value >= 0);

    Rational value{0};
    for (int int_value = abs_min_value; int_value <= abs_bound; ++int_value)
    {
        value = static_cast<Rational>(int_value);
        if (lb <= value && value <= ub && bounds.is_allowed(models, value))
        {
            break;
        }

        value = static_cast<Rational>(-int_value);
        if (lb <= value && value <= ub && bounds.is_allowed(models, value))
        {
            break;
        }
    }

    return bounds.is_allowed(models, value) ? value : std::optional<Rational>{};
}

void Linear_arithmetic::decide(Database&, Trail& trail, Variable var)
{
    if (var.type() != Variable::rational)
    {
        return;
    }

    auto models = relevant_models(trail);
    auto& bnds = bounds[var.ord()];

    Rational value =
        cached_values.is_defined(var.ord()) ? cached_values.value(var.ord()) : Rational{0};
    if (!bnds.is_allowed(models, value))
    {
        if (auto int_value = find_integer(models, bnds))
        {
            value = int_value.value();
        }
        else // there is no suitable integer value
        {
            assert(bnds.lower_bound(models).has_value());
            assert(bnds.upper_bound(models).has_value());

            auto lb = bnds.lower_bound(models).value().value();
            auto ub = bnds.upper_bound(models).value().value();

            value = ub;
            while (!bnds.is_allowed(models, value))
            {
                value = lb / Rational{2} + value / Rational{2};
            }
        }
    }

    // decide the value
    assert(bnds.is_allowed(models, value));
    models.owned().set_value(var.ord(), value);
    trail.decide(var);
}

} // namespace perun