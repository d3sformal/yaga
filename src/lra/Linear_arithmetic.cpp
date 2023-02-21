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
    for (auto [var, _] : trail.assigned(trail.decision_level()))
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

bool Linear_arithmetic::replace_watch(Model<Value_type> const& lra_model, Watched_constraint& watch,
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

std::optional<Clause> Linear_arithmetic::replace_watch(Trail& trail, Models_type& models,
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

std::optional<int> Linear_arithmetic::implied(Trail& trail, Models_type const& models,
                                              Constraint_type cons)
{
    if (cons.pred() == Order_predicate::eq)
    {
        return {};
    }

    assert(!cons.empty());
    assert(!models.boolean().is_defined(cons.lit().var().ord()));
    assert(!models.owned().is_defined(cons.vars().front()));
    assert(cons.coef().front() != 0);

    if (implies_lower_bound(cons))
    {
        if (auto lower_bound = bounds[cons.vars().front()].lower_bound(models))
        {
            auto lb = lower_bound.value();
            auto implied_lb = cons.implied_value(models.owned()) / cons.coef().front();
            if (implied_lb < lb.value()) // `cons` implies a worse lower bound
            {
                auto level = trail.decision_level(lb.reason().lit().var());
                assert(level.has_value());
                for (auto var : cons.vars() | std::views::drop(1))
                {
                    level = std::max<int>(
                        level.value(),
                        trail.decision_level(Variable{var, Variable::rational}).value());
                }
                return level;
            }
        }
    }
    else // implies_upper_bound(cons)
    {
        assert(implies_upper_bound(cons));
        assert(!cons.empty());
        assert(!models.boolean().is_defined(cons.lit().var().ord()));
        assert(!models.owned().is_defined(cons.vars().front()));
        assert(cons.coef().front() != 0);

        if (auto upper_bound = bounds[cons.vars().front()].upper_bound(models))
        {
            auto ub = upper_bound.value();
            auto implied_ub = cons.implied_value(models.owned()) / cons.coef().front();
            if (implied_ub > ub.value()) // `cons` implies a worse upper bound
            {
                auto level = trail.decision_level(ub.reason().lit().var());
                assert(level.has_value());
                for (auto var : cons.vars() | std::views::drop(1))
                {
                    level = std::max<int>(
                        level.value(),
                        trail.decision_level(Variable{var, Variable::rational}).value());
                }
                return level;
            }
        }
    }
    return {}; // none, `cons` is not implied by current trail
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
        return true;
    }

    return (cons.coef().front() > 0 && cons.lit().is_negation()) ||
           (cons.coef().front() < 0 && !cons.lit().is_negation());
}

bool Linear_arithmetic::implies_upper_bound(Constraint_type const& cons) const
{
    if (cons.pred() == Order_predicate::eq)
    {
        return true;
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

std::optional<Clause> Linear_arithmetic::unit(Trail& trail, Models_type& models,
                                              Constraint_type& cons)
{
    update_bounds(models, cons);
    if (auto conflict = check_bounds(trail, models, bounds[cons.vars().front()]))
    {
        return conflict;
    }
    return {};
}

void Linear_arithmetic::normalize(Linear_polynomial& poly)
{
    // sort by variable
    std::sort(poly.begin(), poly.end(), [&](auto lhs, auto rhs) { return lhs.first < rhs.first; });

    // combine coefficients if they belong to the same variable
    auto out_it = poly.begin();
    for (auto [var, coef] : poly | std::views::drop(1))
    {
        if (out_it->first != var)
        {
            if (out_it->second != 0) // drop variables with 0 coefficient
            {
                ++out_it;
            }
            out_it->first = var;
            out_it->second = coef;
        }
        else
        {
            out_it->second += coef;
        }
    }

    if (!poly.empty() && out_it->second != 0) // drop variables with 0 coefficient
    {
        ++out_it;
    }
    poly.variables.erase(out_it, poly.end());
}

Linear_arithmetic::Linear_polynomial Linear_arithmetic::polynomial(Constraint_type const& cons,
                                                                   Value_type mult)
{
    Linear_polynomial poly;
    auto var_it = cons.vars().begin();
    auto coef_it = cons.coef().begin();
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        poly.variables.emplace_back(*var_it, *coef_it * mult);
    }
    poly.constant = -cons.rhs() * mult;
    return poly;
}

Linear_arithmetic::Linear_polynomial Linear_arithmetic::fm(Linear_polynomial&& poly,
                                                           Constraint_type const& cons)
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
    normalize(poly);

    assert(std::find_if(poly.begin(), poly.end(),
                        [&](auto var) { return var.first == *cons_var_it; }) == poly.end());
    return poly;
}

Linear_arithmetic::Constraint_type Linear_arithmetic::eliminate(Trail& trail,
                                                                Constraint_type const& first,
                                                                Constraint_type const& second)
{
    assert(!first.empty());
    assert(!second.empty());
    assert(first.vars().front() == second.vars().front());
    assert(implies_lower_bound(first));
    assert(implies_upper_bound(second));

    // find predicate of the combination
    Order_predicate pred = Order_predicate::leq;
    if (first.pred() == Order_predicate::eq && second.pred() == Order_predicate::eq &&
        !first.lit().is_negation() && !second.lit().is_negation())
    {
        pred = Order_predicate::eq;
    }
    else if (first.is_strict() || second.is_strict())
    {
        pred = Order_predicate::lt;
    }

    // eliminate the first unassigned variable
    auto poly = fm(polynomial(first, first.coef().front() > 0 ? -1 : 1), second);
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

    // create a new constraint
    auto result =
        constraint(trail, std::views::keys(poly), std::views::values(poly), pred, -poly.constant);
    assert(!result.vars().empty());

    // propagate the new constraint semantically
    auto models = relevant_models(trail);
    if (!models.boolean().is_defined(result.lit().var().ord()))
    {
        propagate(trail, models, result);
    }

    return result;
}

Linear_arithmetic::Value_type Linear_arithmetic::implied_value(Models_type const& models,
                                                               Linear_polynomial const& poly) const
{
    assert(!poly.empty());

    auto var_coef = poly.begin()->second;
    auto bound = -poly.constant;
    for (auto [ord, coef] : poly | std::views::drop(1))
    {
        assert(models.owned().is_defined(ord));
        bound -= coef * models.owned().value(ord);
    }
    return bound / var_coef;
}

std::optional<Linear_arithmetic::Constraint_type>
Linear_arithmetic::find_bound_conflict(Models_type const& models, Linear_polynomial const& poly,
                                       Order_predicate pred)
{
    // compute bound implied by `poly` for the first variable
    auto bound = implied_value(models, poly);
    auto [var_ord, var_coef] = *poly.begin();

    if (var_coef < 0 || pred == Order_predicate::eq) // `bound` is a lower bound
    {
        if (auto upper_bound = bounds[var_ord].upper_bound(models))
        {
            auto ub = upper_bound.value();
            auto is_strict = ub.reason().is_strict() || pred == Order_predicate::lt;
            if (ub.value() < bound || (ub.value() == bound && is_strict))
            {
                return ub.reason();
            }
        }
    }

    if (var_coef > 0 || pred == Order_predicate::eq) // `bound` is an upper bound
    {
        if (auto lower_bound = bounds[var_ord].lower_bound(models))
        {
            auto lb = lower_bound.value();
            auto is_strict = lb.reason().is_strict() || pred == Order_predicate::lt;
            if (lb.value() > bound || (lb.value() == bound && is_strict))
            {
                return lb.reason();
            }
        }
    }

    return {};
}

Clause Linear_arithmetic::resolve_bound_conflict(Trail& trail, Constraint_type const& cons)
{
    Clause conflict{cons.lit().negate()};

    auto models = relevant_models(trail);
    auto poly = polynomial(cons, cons.coef().front() > 0 ? -1 : 1);
    auto pred = cons.pred();
    if (cons.lit().is_negation())
    {
        if (pred == Order_predicate::leq)
        {
            pred = Order_predicate::lt;
        }
        else if (pred == Order_predicate::lt)
        {
            pred = Order_predicate::leq;
        }
    }

    // combine current predicate `pred` with a predicate of other constraint
    auto combine_pred = [](Order_predicate pred, Constraint_type const& other) {
        if (pred == Order_predicate::eq && other.pred() == Order_predicate::eq)
        {
            return Order_predicate::eq;
        }
        else if (pred != Order_predicate::lt && !other.is_strict())
        {
            return Order_predicate::leq;
        }
        else
        {
            return Order_predicate::lt;
        }
    };

    while (!poly.empty())
    {
        // Move the top level variable to the front.
        // In the first iteration, the first variable will be unassigned. In subsequent iterations,
        // all variables will be assigned.
        int top_level = trail.decision_level(Variable{poly.begin()->first, Variable::rational})
                            .value_or(trail.decision_level());
        auto top_it = poly.begin();
        for (auto it = ++poly.begin(); it != poly.end(); ++it)
        {
            Variable new_var{it->first, Variable::rational};
            if (trail.decision_level(new_var).value() > top_level)
            {
                top_level = trail.decision_level(new_var).value();
                top_it = it;
            }
        }
        std::iter_swap(top_it, poly.begin());

        // eliminate the first variable if it is in a bound conflict
        if (auto reason = find_bound_conflict(models, poly, pred))
        {
            poly = fm(std::move(poly), reason.value());
            pred = combine_pred(pred, reason.value());
            conflict.push_back(reason.value().lit().negate());
        }
        else
        {
            break;
        }
    }
    assert(conflict.size() >= 2);
    assert(eval(models.boolean(), conflict) == false);

    if (poly.empty())
    {
        return conflict;
    }

    // sort the polynomial by decision level
    std::sort(poly.begin(), poly.end(), [&](auto lhs, auto rhs) {
        Variable lhs_var{lhs.first, Variable::rational};
        Variable rhs_var{rhs.first, Variable::rational};
        return trail.decision_level(lhs_var).value() > trail.decision_level(rhs_var).value();
    });

    // create a linear constraint from `poly` and `pred` (head of the implication)
    auto head =
        constraint(trail, std::views::keys(poly), std::views::values(poly), pred, -poly.constant);
    assert(!head.empty());
    if (!models.boolean().is_defined(head.lit().var().ord()))
    {
        propagate(trail, models, head);
    }
    assert(eval(models.boolean(), head.lit()) == false);
    assert(eval(models.owned(), head) == false);

    // add the constraint as head of the implication
    conflict.push_back(head.lit());
    assert(eval(models.boolean(), conflict) == false);
    return conflict;
}

std::optional<Clause> Linear_arithmetic::check_bound_conflict(Trail& trail, Models_type& models,
                                                              Bounds_type& bounds)
{
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

    return resolve_bound_conflict(trail, lb.reason());
}

std::optional<Clause>
Linear_arithmetic::check_inequality_conflict(Trail& trail, Models_type& models, Bounds_type& bounds)
{
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

    // if `L < D` is non-trivial (i.e., it contains at least one variable)
    if (lb.reason().vars().size() > 1 || inequality.value().reason().vars().size() > 1)
    {
        // create and propagate `L < D` semantically
        auto cons = eliminate(trail, lb.reason(), inequality.value().reason());
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
        auto cons = eliminate(trail, inequality.value().reason(), ub.reason());
        if (!cons.empty())
        {
            assert(eval(models.owned(), cons) == false);
            assert(eval(models.boolean(), cons.lit()) == false);
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

std::optional<Linear_arithmetic::Value_type>
Linear_arithmetic::find_integer(Models_type const& models, Bounds_type& bounds)
{
    auto abs = [](int val) -> int {
        if (val == std::numeric_limits<int>::min())
        {
            return std::numeric_limits<int>::max();
        }
        return val >= 0 ? val : -val;
    };

    Value_type lb{std::numeric_limits<int>::lowest()};
    Value_type ub{std::numeric_limits<int>::max()};
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
    if (lb <= Value_type{0} && ub >= Value_type{0})
    {
        abs_bound = std::max<int>(abs(static_cast<int>(lb)), static_cast<int>(ub));
    }
    else if (lb > Value_type{0})
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

    Value_type value{0};
    for (int int_value = abs_min_value; int_value <= abs_bound; ++int_value)
    {
        value = static_cast<Value_type>(int_value);
        if (lb <= value && value <= ub && bounds.is_allowed(models, value))
        {
            break;
        }

        value = static_cast<Value_type>(-int_value);
        if (lb <= value && value <= ub && bounds.is_allowed(models, value))
        {
            break;
        }
    }

    return bounds.is_allowed(models, value) ? value : std::optional<Value_type>{};
}

void Linear_arithmetic::decide(Database&, Trail& trail, Variable var)
{
    if (var.type() != Variable::rational)
    {
        return;
    }

    auto models = relevant_models(trail);
    auto& bnds = bounds[var.ord()];

    Value_type value =
        cached_values.is_defined(var.ord()) ? cached_values.value(var.ord()) : Value_type{0};
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
                value = lb / Value_type{2} + value / Value_type{2};
            }
        }
    }

    // decide the value
    assert(bnds.is_allowed(models, value));
    models.owned().set_value(var.ord(), value);
    trail.decide(var);
}

} // namespace perun