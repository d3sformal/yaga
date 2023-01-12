#include "Linear_arithmetic.h"

namespace perun {

void Linear_arithmetic::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::rational)
    {
        bounds.resize(num_vars);
        watched.resize(num_vars);
    }
}

std::optional<Clause> Linear_arithmetic::propagate(Database&, Trail& trail)
{
    std::vector<int> assigned;
    auto& bool_model = trail.model<bool>(Variable::boolean);
    auto& lra_model = trail.model<Value_type>(Variable::rational);

    // check for new unit constraints on the trail
    for (auto [var, _] : trail.assigned(trail.decision_level()))
    {
        if (var.type() == Variable::boolean && !constraints[var.ord()].empty())
        {
            auto cons = constraints[var.ord()];
            if (lra_model.is_defined(cons.vars().front()))
            {
                assert(cons.eval(lra_model) == eval(bool_model, cons.lit()));
                continue; // skip fully assigned constraints
            }

            if (is_unit(lra_model, cons))
            {
                if (auto conflict = unit(assigned, trail, bool_model, lra_model, cons))
                {
                    return conflict;
                }
            }
        }
    }

    // check whether all unit constraints are consistent after new assignments
    for (auto [var, _] : trail.assigned(trail.decision_level()))
    {
        if (var.type() == Variable::rational)
        {
            assigned.push_back(var.ord());
        }
    }

    std::optional<Clause> conflict;
    while (!assigned.empty() && !conflict)
    {
        auto lra_var_ord = assigned.back();
        assigned.pop_back();

        conflict = replace_watch(assigned, trail, bool_model, lra_model, lra_var_ord);
    }
    return conflict;
}

void Linear_arithmetic::watch(Constraint_type& cons)
{
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

    // move the assigned variable to the second position
    if (cons.vars()[1] != lra_var_ord)
    {
        std::swap(cons.vars()[0], cons.vars()[1]);
        std::swap(cons.coef()[0], cons.coef()[1]);
    }
    assert(cons.vars()[1] == lra_var_ord);

    // find an unassigned variable to watch
    auto var_it = cons.vars().begin() + 2;
    auto coef_it = cons.coef().begin() + 2;
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        assert(coef_it != cons.coef().end());
        if (!lra_model.is_defined(*var_it))
        {
            std::iter_swap(++cons.vars().begin(), var_it);
            std::iter_swap(++cons.coef().begin(), coef_it);
            watched[cons.vars()[1]].push_back(cons);
            break;
        }
    }

    return cons.vars()[1] != lra_var_ord;
}

std::optional<Clause> Linear_arithmetic::replace_watch(std::vector<int>& assigned, Trail& trail,
                                                       Model<bool>& bool_model,
                                                       Model<Value_type>& lra_model,
                                                       int lra_var_ord)
{
    assert(lra_model.is_defined(lra_var_ord));

    auto& watchlist = watched[lra_var_ord];
    for (std::size_t i = 0; i < watchlist.size();)
    {
        auto& cons = watchlist[i];

        if (replace_watch(lra_model, cons, lra_var_ord))
        {
            // remove the watch
            std::swap(watchlist[i], watchlist.back());
            watchlist.pop_back();
        }
        else // cons is unit or fully assigned
        {
            if (bool_model.is_defined(cons.lit().var().ord())) // cons is on the trail
            {
                if (lra_model.is_defined(cons.vars().front())) // cons is fully assigned
                {
                    assert(cons.eval(lra_model) == eval(bool_model, cons.lit()));
                }
                else if (auto conflict = unit(assigned, trail, bool_model, lra_model, cons))
                {
                    return conflict;
                }
            }
            else // cons is *not* on the trail
            {
                if (lra_model.is_defined(cons.vars().front())) // cons is fully assigned
                {
                    propagate(trail, bool_model, lra_model, cons);
                }
            }
            ++i;
        }
    }
    return {}; // no conflict
}

void Linear_arithmetic::update_bounds(Model<bool> const& bool_model,
                                      Model<Value_type> const& lra_model, Constraint_type& cons)
{
    assert(!cons.empty());
    assert(!lra_model.is_defined(cons.vars().front()));
    assert(bool_model.is_defined(cons.lit().var().ord()));
    assert(cons.coef().front() != 0);

    auto value = cons.implied_value(lra_model) / cons.coef().front();
    // find constraint that should be true in current model (according to bool_model)
    auto actual_cons = perun::eval(bool_model, cons.lit()).value() ? cons : cons.negate();

    if (implies_equality(actual_cons))
    {
        bounds[cons.vars().front()].add_lower_bound(lra_model, {value, actual_cons});
        bounds[cons.vars().front()].add_upper_bound(lra_model, {value, actual_cons});
    }
    else if (implies_inequality(actual_cons))
    {
        bounds[cons.vars().front()].add_inequality({value, actual_cons});
    }
    else if (implies_lower_bound(actual_cons))
    {
        bounds[cons.vars().front()].add_lower_bound(lra_model, {value, actual_cons});
    }
    else // upper bound
    {
        assert(implies_upper_bound(actual_cons));
        bounds[cons.vars().front()].add_upper_bound(lra_model, {value, actual_cons});
    }
}

bool Linear_arithmetic::implies_equality(Constraint_type const& cons) const
{
    return cons.pred() == Order_predicate::EQ && !cons.lit().is_negation();
}

bool Linear_arithmetic::implies_inequality(Constraint_type const& cons) const
{
    return cons.pred() == Order_predicate::EQ && cons.lit().is_negation();
}

bool Linear_arithmetic::implies_lower_bound(Constraint_type const& cons) const
{
    if (cons.pred() == Order_predicate::EQ)
    {
        return false;
    }

    return (cons.coef().front() > 0 && cons.lit().is_negation()) ||
           (cons.coef().front() < 0 && !cons.lit().is_negation());
}

bool Linear_arithmetic::implies_upper_bound(Constraint_type const& cons) const
{
    if (cons.pred() == Order_predicate::EQ)
    {
        return false;
    }

    return (cons.coef().front() < 0 && cons.lit().is_negation()) ||
           (cons.coef().front() > 0 && !cons.lit().is_negation());
}

std::optional<Clause> Linear_arithmetic::check_bounds(Trail& trail, Model<bool>& bool_model,
                                                      Model<Value_type> const& lra_model,
                                                      Bounds<Value_type>& bounds)
{
    if (auto conflict = check_bound_conflict(trail, bool_model, lra_model, bounds))
    {
        return conflict;
    }

    if (auto conflict = check_inequality_conflict(bool_model, lra_model, bounds))
    {
        return conflict;
    }
    return {}; // no conflict
}

std::optional<Linear_arithmetic::Value_type>
Linear_arithmetic::check_equality(Model<Value_type> const& lra_model, Bounds<Value_type>& bounds)
{
    auto lb = bounds.lower_bound(lra_model);
    auto ub = bounds.upper_bound(lra_model);
    if (lb.value() == ub.value() && !lb.reason().is_strict() && !ub.reason().is_strict())
    {
        return lb.value();
    }
    return {};
}

std::optional<Clause> Linear_arithmetic::unit(std::vector<int>& assigned, Trail& trail,
                                              Model<bool>& bool_model, Model<Value_type>& lra_model,
                                              Constraint_type& cons)
{
    update_bounds(bool_model, lra_model, cons);
    if (auto conflict = check_bounds(trail, bool_model, lra_model, bounds[cons.vars().front()]))
    {
        return conflict;
    }

    if (auto value = check_equality(lra_model, bounds[cons.vars().front()]))
    {
        // propagate the value to trail
        lra_model.set_value(cons.vars().front(), value.value());
        trail.propagate(Variable{cons.vars().front(), Variable::rational}, nullptr,
                        trail.decision_level());
        // stop watching the variable in all constraints
        assigned.push_back(cons.vars().front());
    }
    return {};
}

std::optional<Clause> Linear_arithmetic::check_bound_conflict(Trail& trail, Model<bool>& bool_model,
                                                              Model<Value_type> const& lra_model,
                                                              Bounds<Value_type>& bounds)
{
    auto lb = bounds.lower_bound(lra_model);
    auto ub = bounds.upper_bound(lra_model);
    auto is_either_strict = lb.reason().is_strict() || ub.reason().is_strict();
    if (lb.value() < ub.value() || (lb.value() == ub.value() && !is_either_strict))
    {
        return {}; // no conflict
    }
    assert(!lb.reason().empty());
    assert(!ub.reason().empty());
    assert(lb.reason().vars().front() == ub.reason().vars().front());
    assert(!lra_model.is_defined(lb.reason().vars().front()));

    // eliminate the unassigned variable in lb and ub using the Fourier-Motzkin method
    auto pred = is_either_strict ? Order_predicate::LT : Order_predicate::LEQ;
    auto lb_mult = lb.reason().coef().front() < 0 ? Value_type{1} : Value_type{-1};
    auto ub_mult = std::abs(lb.reason().coef().front()) / ub.reason().coef().front();

    // compute `lb_mult * polynomial(lb) + ub_mult * polynomial(ub)`
    auto rhs = lb.reason().rhs() * lb_mult + ub.reason().rhs() * ub_mult;
    std::unordered_map<int, Value_type> prod;
    auto var_it = ++lb.reason().vars().begin(); // skip the unassigned variable
    auto coef_it = ++lb.reason().coef().begin();
    for (; var_it != lb.reason().vars().end(); ++var_it, ++coef_it)
    {
        prod.insert({*var_it, *coef_it * lb_mult});
    }

    var_it = ++ub.reason().vars().begin();
    coef_it = ++ub.reason().coef().begin();
    for (; var_it != ub.reason().vars().end(); ++var_it, ++coef_it)
    {
        auto [it, _] = prod.insert({*var_it, Value_type{0}});
        it->second += *coef_it * ub_mult;
    }

    // L <= x && x <= U -> L < U
    auto cons = constraint(lra_model, std::views::keys(prod), std::views::values(prod), pred, rhs);

    // semantically propagate the new literal so that the conflict clause evaluates to false even in
    // the boolean model
    propagate(trail, bool_model, lra_model, cons);

    return Clause{lb.reason().lit().negate(), ub.reason().lit().negate(), cons.lit()};
}

std::optional<Clause> Linear_arithmetic::check_inequality_conflict(Model<bool> const&,
                                                                   Model<Value_type> const&,
                                                                   Bounds<Value_type>&)
{
    return {}; // TODO
}

void Linear_arithmetic::propagate(Trail& trail, Model<bool>& bool_model,
                                  Model<Value_type> const& lra_model, Constraint_type const& cons)
{
    assert(!eval(bool_model, cons.lit()));

    // find decision level of the propagation
    int dec_level = 0;
    for (auto var_ord : cons.vars())
    {
        auto level = trail.decision_level(Variable{var_ord, Variable::rational});
        assert(level.has_value());
        dec_level = std::max<int>(dec_level, level.value());
    }

    // propagate the boolean variable of the constraint
    auto value = cons.eval(lra_model);
    bool_model.set_value(cons.lit().var().ord(), cons.lit().is_negation() ^ value);
    trail.propagate(cons.lit().var(), /*reason=*/nullptr, dec_level);
}

void Linear_arithmetic::decide(Database&, Trail&, Variable)
{
    // TODO
}

} // namespace perun