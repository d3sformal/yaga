#include "Linear_arithmetic.h"

namespace perun {

void Linear_arithmetic::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::rational)
    {
        bounds.resize(num_vars);
        watched.resize(num_vars);
    }
    else if (type == Variable::boolean)
    {
        constraints.resize(num_vars);
    }
}

std::optional<Clause> Linear_arithmetic::propagate(Database&, Trail& trail)
{
    auto models = relevant_models(trail);

    // detect new unit constraints on the trail
    Assigned_stack assigned;
    for (auto [var, _] : trail.assigned(trail.decision_level()))
    {
        if (var.type() == Variable::boolean && !constraints[var.ord()].empty())
        {
            auto cons = constraints[var.ord()];
            if (models.owned().is_defined(cons.vars().front()))
            {
                assert(eval(models.owned(), cons) == eval(models.boolean(), cons.lit()));
                continue; // skip fully assigned constraints
            }

            if (is_unit(models.owned(), cons))
            {
                if (auto conflict = unit(assigned, trail, models, cons))
                {
                    return conflict;
                }
            }
        }
        else if (var.type() == Variable::rational)
        {
            assigned.emplace_back(var, std::optional<Value_type>{});
        }
    }

    std::optional<Clause> conflict;
    while (!assigned.empty() && !conflict)
    {
        auto [var, val] = assigned.back();
        assigned.pop_back();
        if (val)
        {
            if (!models.owned().is_defined(var.ord()))
            {
                models.owned().set_value(var.ord(), val.value());
                trail.propagate(var, nullptr, trail.decision_level());
            }
            else
            {
                assert(models.owned().value(var.ord()) == val.value());
            }
        }
        assert(var.type() == Variable::rational);
        conflict = replace_watch(assigned, trail, models, var.ord());
    }
    return conflict;
}

void Linear_arithmetic::watch(Constraint_type& cons)
{
    assert(!cons.empty());

    watched[cons.vars()[0]].push_back(cons);
    if (cons.size() > 1)
    {
        watched[cons.vars()[1]].push_back(cons);
    }
}

void Linear_arithmetic::watch(Constraint_type& cons, Model<Value_type> const& model)
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

bool Linear_arithmetic::replace_watch(Model<Value_type> const& lra_model, Constraint_type& cons,
                                      int lra_var_ord)
{
    if (cons.size() <= 1)
    {
        assert(cons.vars().front() == lra_var_ord);
        return false;
    }

    // if both watched variables are assigned, the constraint is fully assigned
    if (lra_model.is_defined(cons.vars()[0]) && lra_model.is_defined(cons.vars()[1]))
    {
        assert(std::all_of(cons.vars().begin(), cons.vars().end(), [&](auto var) {
            return lra_model.is_defined(var);
        }));
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
    auto var_it = cons.vars().begin() + 2;
    auto coef_it = cons.coef().begin() + 2;
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        assert(coef_it != cons.coef().end());
        if (!lra_model.is_defined(*var_it))
        {
            std::iter_swap(rep_var_it, var_it);
            std::iter_swap(rep_coef_it, coef_it);
            watched[*rep_var_it].push_back(cons);
            break;
        }
    }

    return *rep_var_it != lra_var_ord;
}

std::optional<Clause> Linear_arithmetic::replace_watch(Assigned_stack& assigned, Trail& trail,
                                                       Models_type& models, int lra_var_ord)
{
    assert(models.owned().is_defined(lra_var_ord));

    auto& watchlist = watched[lra_var_ord];
    for (std::size_t i = 0; i < watchlist.size();)
    {
        auto& cons = watchlist[i];

        if (replace_watch(models.owned(), cons, lra_var_ord))
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
                else if (auto conflict = unit(assigned, trail, models, cons))
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

void Linear_arithmetic::update_bounds(Models_type const& models, Constraint_type& cons)
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

bool Linear_arithmetic::implies_equality(Constraint_type const& cons) const
{
    return cons.pred() == Order_predicate::eq && !cons.lit().is_negation();
}

bool Linear_arithmetic::implies_inequality(Constraint_type const& cons) const
{
    return cons.pred() == Order_predicate::eq && cons.lit().is_negation();
}

bool Linear_arithmetic::implies_lower_bound(Constraint_type const& cons) const
{
    if (cons.pred() == Order_predicate::eq)
    {
        return false;
    }

    return (cons.coef().front() > 0 && cons.lit().is_negation()) ||
           (cons.coef().front() < 0 && !cons.lit().is_negation());
}

bool Linear_arithmetic::implies_upper_bound(Constraint_type const& cons) const
{
    if (cons.pred() == Order_predicate::eq)
    {
        return false;
    }

    return (cons.coef().front() < 0 && cons.lit().is_negation()) ||
           (cons.coef().front() > 0 && !cons.lit().is_negation());
}

std::optional<Clause> Linear_arithmetic::check_bounds(Trail& trail, Models_type& models,
                                                      Bounds_type& bounds)
{
    if (auto conflict = check_bound_conflict(trail, models, bounds))
    {
        return conflict;
    }

    if (auto conflict = check_inequality_conflict(trail, models, bounds))
    {
        return conflict;
    }
    return {}; // no conflict
}

std::optional<Linear_arithmetic::Value_type>
Linear_arithmetic::check_equality(Models_type const& models, Bounds_type& bounds)
{
    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
    if (lb.value() == ub.value() && !lb.reason().is_strict() && !ub.reason().is_strict())
    {
        return lb.value();
    }
    return {};
}

std::optional<Clause> Linear_arithmetic::unit(Assigned_stack& assigned, Trail& trail,
                                              Models_type& models, Constraint_type& cons)
{
    update_bounds(models, cons);
    if (auto conflict = check_bounds(trail, models, bounds[cons.vars().front()]))
    {
        return conflict;
    }

    if (auto value = check_equality(models, bounds[cons.vars().front()]))
    {
        assigned.emplace_back(Variable{cons.vars().front(), Variable::rational}, value);
    }
    return {};
}

Linear_arithmetic::Constraint_type Linear_arithmetic::eliminate(Trail& trail,
                                                                Constraint_type const& first,
                                                                Constraint_type const& second)
{
    assert(!first.empty());
    assert(!second.empty());
    assert(first.vars().front() == second.vars().front());
    assert(!trail.model<Value_type>(Variable::rational).is_defined(first.vars().front()));

    // find predicate of the combination
    auto pred = Order_predicate::leq;
    if (first.pred() == Order_predicate::eq && second.pred() == Order_predicate::eq &&
        !first.lit().is_negation() && !second.lit().is_negation())
    {
        pred = Order_predicate::eq;
    }
    else if (first.is_strict() || second.is_strict())
    {
        pred = Order_predicate::lt;
    }

    // compute constants such that `poly(first) * first_mult + poly(second) * second_mult`
    // eliminates the first variable
    auto first_mult = first.coef().front() < Value_type{0} ? Value_type{1} : Value_type{-1};
    auto second_mult = -first_mult * first.coef().front() / second.coef().front();

    // compute `poly(first) * first_mult + poly(second) * second_mult`
    auto rhs = first.rhs() * first_mult + second.rhs() * second_mult;
    std::unordered_map<int, Value_type> prod;
    for (auto [cons_ptr, mult] : {std::pair{&first, first_mult}, std::pair{&second, second_mult}})
    {
        auto var_it = ++cons_ptr->vars().begin(); // skip the unassigned variable
        auto coef_it = ++cons_ptr->coef().begin();
        for (; var_it != cons_ptr->vars().end(); ++var_it, ++coef_it)
        {
            auto [it, _] = prod.insert({*var_it, Value_type{0}});
            it->second += *coef_it * mult;
        }
    }

    // remove variables with 0 coefficient
    for (auto it = prod.begin(); it != prod.end();)
    {
        if (it->second == Value_type{0})
        {
            it = prod.erase(it);
        }
        else 
        {
            ++it;
        }
    }

    if (prod.empty())
    {
        return {};
    }

    return constraint(trail, std::views::keys(prod), std::views::values(prod), pred, rhs);
}

std::optional<Clause> Linear_arithmetic::check_bound_conflict(Trail& trail, Models_type& models,
                                                              Bounds_type& bounds)
{
    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
    auto is_either_strict = lb.reason().is_strict() || ub.reason().is_strict();
    if (lb.value() < ub.value() || (lb.value() == ub.value() && !is_either_strict))
    {
        return {}; // no conflict
    }

    Clause conflict{lb.reason().lit().negate(), ub.reason().lit().negate()};

    // if `lb and ub` imply `false`
    if (lb.reason().size() == 1 && ub.reason().size() == 1)
    {
        return conflict;
    }

    // create `L <= U` and propagate the literal semantically so that the conflict clause is false
    auto cons = eliminate(trail, lb.reason(), ub.reason());
    if (cons.empty())
    {
        return conflict;
    }

    // propagate the new constraint semantically
    assert(!cons.vars().empty());
    if (!models.boolean().is_defined(cons.lit().var().ord()))
    {
        propagate(trail, models, cons);
    }

    conflict.push_back(cons.lit());
    assert(eval(models.boolean(), cons.lit()) == eval(models.owned(), cons));
    return conflict;
}

std::optional<Clause> Linear_arithmetic::check_inequality_conflict(Trail& trail,
                                                                   Models_type& models,
                                                                   Bounds_type& bounds)
{
    // check if `L <= x && x <= U` and `L = U` where `x` is the unassigned variable
    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
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

    // if `L < D` is non-trivial (i.e., it contains at least one variable)
    if (lb.reason().vars().size() > 1 || inequality.value().reason().vars().size() > 1)
    {
        // create and propagate `L < D` semantically
        auto cons = eliminate(trail, lb.reason(), inequality.value().reason());
        if (!cons.empty())
        {
            propagate(trail, models, cons);
            conflict.push_back(cons.lit());
        }
    }

    // if `D < U` is non-trivial (i.e., it contains at least one variable)
    if (ub.reason().vars().size() > 1 || inequality.value().reason().vars().size() > 1)
    {
        // create and propagate `D < U` semantically
        auto cons = eliminate(trail, inequality.value().reason(), ub.reason());
        if (!cons.empty())
        {
            propagate(trail, models, cons);
            conflict.push_back(cons.lit());
        }
    }

    return conflict;
}

void Linear_arithmetic::propagate(Trail& trail, Models_type& models, Constraint_type const& cons)
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

bool Linear_arithmetic::is_new(Models_type const& models, Variable var) const
{
    return (var.type() == Variable::boolean &&
            var.ord() >= static_cast<int>(models.boolean().num_vars())) ||
           (var.type() == Variable::rational &&
            var.ord() >= static_cast<int>(models.owned().num_vars()));
}

void Linear_arithmetic::add_variable(Trail& trail, Models_type const& models, Variable var)
{
    if (is_new(models, var))
    {
        trail.resize(var.type(), var.ord() + 1);
    }
}

int Linear_arithmetic::convert(Value_type value) const
{
    if (value > std::numeric_limits<int>::max())
    {
        return std::numeric_limits<int>::max();
    }
    else if (value < std::numeric_limits<int>::min())
    {
        return std::numeric_limits<int>::min();
    }
    return static_cast<int>(value);
}

void Linear_arithmetic::decide(Database&, Trail& trail, Variable var)
{
    if (var.type() != Variable::rational)
    {
        return;
    }

    auto models = relevant_models(trail);
    auto& bnds = bounds[var.ord()];

    auto abs = [](int val) -> int {
        if (val == std::numeric_limits<int>::min())
        {
            return std::numeric_limits<int>::max();
        }
        return val >= 0 ? val : -val;
    };

    Value_type value{0};
    if (!bnds.is_allowed(models, value))
    {
        // find an allowed value
        auto left = bnds.lower_bound(models).value();
        auto right = bnds.upper_bound(models).value();

        // try integer values first
        int abs_min_value = 0;
        int abs_bound = 0;
        if (left <= Value_type{0} && right >= Value_type{0})
        {
            abs_bound = std::max<int>(abs(convert(left)), convert(right));
        }
        else if (left > Value_type{0})
        {
            abs_min_value = convert(left);
            abs_bound = convert(right);
        }
        else // left <= right < 0
        {
            abs_bound = abs(convert(left));
            abs_min_value = abs(convert(right));
        }

        for (int int_value = abs_min_value; int_value <= abs_bound; ++int_value)
        {
            value = static_cast<Value_type>(int_value);
            if (left <= value && value <= right && bnds.is_allowed(models, value))
            {
                break;
            }

            value = static_cast<Value_type>(-int_value);
            if (left <= value && value <= right && bnds.is_allowed(models, value))
            {
                break;
            }
        }

        // if there is no suitable integer value
        if (!bnds.is_allowed(models, value))
        {
            value = right;
            while (!bnds.is_allowed(models, value))
            {
                value = left / Value_type{2} + value / Value_type{2};
            }
        }
    }

    // decide the value
    assert(bnds.is_allowed(models, value));
    models.owned().set_value(var.ord(), value);
    trail.decide(var);
}

} // namespace perun