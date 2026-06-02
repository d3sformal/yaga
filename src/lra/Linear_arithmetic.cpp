#include "Linear_arithmetic.h"

#include <array>
#include <limits>
#include <unordered_set>

namespace yaga {

namespace {

using Models = Linear_arithmetic::Models;
using Constraint = Linear_arithmetic::Constraint;
using Bound = Implied_value<Rational>;

struct Decision_interval {
    std::optional<Rational> lb;
    bool lb_strict = false;
    std::optional<Rational> ub;
    bool ub_strict = false;
    std::vector<Rational> neq;
};

void add_lower_bound(Decision_interval& interval, Rational const& value, bool strict)
{
    if (!interval.lb || *interval.lb < value ||
        (*interval.lb == value && strict && !interval.lb_strict))
    {
        interval.lb = value;
        interval.lb_strict = strict;
    }
}

void add_upper_bound(Decision_interval& interval, Rational const& value, bool strict)
{
    if (!interval.ub || value < *interval.ub ||
        (*interval.ub == value && strict && !interval.ub_strict))
    {
        interval.ub = value;
        interval.ub_strict = strict;
    }
}

bool interval_allows(Decision_interval const& interval, Rational const& value)
{
    if (interval.lb &&
        !(interval.lb.value() < value || (interval.lb.value() == value && !interval.lb_strict)))
    {
        return false;
    }
    if (interval.ub &&
        !(value < interval.ub.value() || (value == interval.ub.value() && !interval.ub_strict)))
    {
        return false;
    }
    return std::ranges::find(interval.neq, value) == interval.neq.end();
}

Rational lower_seed(Rational const& value, bool strict)
{
    auto result = value.ceil();
    if (strict && result == value)
    {
        result += 1;
    }
    return result;
}

Rational upper_seed(Rational const& value, bool strict)
{
    auto result = value.floor();
    if (strict && result == value)
    {
        result -= 1;
    }
    return result;
}

Rational distance(Rational const& lhs, Rational const& rhs)
{
    return lhs < rhs ? rhs - lhs : lhs - rhs;
}

int count_integer_candidates(Models const& models, Linear_arithmetic::Bounds_type& bounds, int limit)
{
    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
    if (!lb || !ub)
    {
        return limit;
    }

    auto first = lower_seed(lb->value(), lb->is_strict());
    auto last = upper_seed(ub->value(), ub->is_strict());
    if (last < first)
    {
        return 0;
    }

    if (last - first >= Rational{limit})
    {
        return limit;
    }

    int count = 0;
    for (Rational value = first; value <= last && count < limit; value += 1)
    {
        if (bounds.is_allowed(models, value))
        {
            ++count;
        }
    }
    return count;
}

template <typename Allowed>
std::optional<Rational> choose_candidate(Decision_interval const& interval,
                                         Rational const& preferred_value, Allowed&& allowed)
{
    std::vector<Rational> seeds;
    seeds.reserve(8);
    auto add_seed = [&](Rational const& value) {
        if (value.isInteger())
        {
            seeds.push_back(value);
        }
        else
        {
            seeds.push_back(value.floor());
            seeds.push_back(value.ceil());
        }
    };

    add_seed(preferred_value);
    if (interval.lb)
    {
        seeds.push_back(lower_seed(*interval.lb, interval.lb_strict));
    }
    if (interval.ub)
    {
        seeds.push_back(upper_seed(*interval.ub, interval.ub_strict));
    }
    if (interval.lb && interval.ub)
    {
        add_seed((*interval.lb + *interval.ub) / Rational{2});
    }

    for (auto const& seed : seeds)
    {
        if (allowed(seed))
        {
            return seed;
        }
    }

    constexpr int radius_limit = 64;
    for (int delta = 1; delta <= radius_limit; ++delta)
    {
        Rational const step{delta};
        for (auto const& seed : seeds)
        {
            auto above = seed + step;
            if (allowed(above))
            {
                return above;
            }

            auto below = seed - step;
            if (allowed(below))
            {
                return below;
            }
        }
    }
    return {};
}

void merge_interval(Decision_interval& into, Decision_interval const& other)
{
    if (other.lb)
    {
        add_lower_bound(into, *other.lb, other.lb_strict);
    }
    if (other.ub)
    {
        add_upper_bound(into, *other.ub, other.ub_strict);
    }
    into.neq.insert(into.neq.end(), other.neq.begin(), other.neq.end());
}

template <typename Value_of>
std::optional<Decision_interval> project_interval(Constraint const& cons, int var_ord,
                                                  Value_of&& value_of)
{
    Rational rhs = cons.rhs();
    std::optional<Rational> coeff;
    auto var_it = cons.vars().begin();
    auto coef_it = cons.coef().begin();
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        if (*var_it == var_ord)
        {
            coeff = *coef_it;
            continue;
        }
        rhs -= *coef_it * value_of(*var_it);
    }

    if (!coeff || *coeff == 0)
    {
        return {};
    }

    Decision_interval interval;
    auto bound = rhs / *coeff;
    if (cons.pred() == Order_predicate::eq)
    {
        if (cons.lit().is_negation())
        {
            interval.neq.push_back(bound);
        }
        else
        {
            add_lower_bound(interval, bound, false);
            add_upper_bound(interval, bound, false);
        }
        return interval;
    }

    if (*coeff > 0)
    {
        if (!cons.lit().is_negation())
        {
            add_upper_bound(interval, bound, cons.pred() == Order_predicate::lt);
        }
        else
        {
            add_lower_bound(interval, bound, cons.pred() == Order_predicate::leq);
        }
    }
    else
    {
        if (!cons.lit().is_negation())
        {
            add_lower_bound(interval, bound, cons.pred() == Order_predicate::lt);
        }
        else
        {
            add_upper_bound(interval, bound, cons.pred() == Order_predicate::leq);
        }
    }
    return interval;
}

template <typename Value_of>
bool satisfies(Constraint const& cons, Value_of&& value_of)
{
    auto rhs = cons.rhs();
    auto var_it = cons.vars().begin();
    auto coef_it = cons.coef().begin();
    for (; var_it != cons.vars().end(); ++var_it, ++coef_it)
    {
        rhs -= *coef_it * value_of(*var_it);
    }
    return cons.lit().is_negation() ^ cons.pred()(Rational{0}, rhs);
}

std::optional<Literal> ensure_assignment_literal(Linear_arithmetic* lra, Trail& trail,
                                                 Models& models, int var_ord)
{
    if (!models.owned().is_defined(var_ord))
    {
        return {};
    }

    std::array<int, 1> vars{var_ord};
    std::array<Rational, 1> coef{Rational{1}};
    auto eq = lra->constraint(trail, vars, coef, Order_predicate::eq, models.owned().value(var_ord));

    auto current = eval(models.boolean(), eq.lit());
    if (!current.has_value())
    {
        lra->propagate(trail, models, eq);
    }
    assert(eval(models.owned(), eq) == true);
    if (eval(models.boolean(), eq.lit()) != true)
    {
        return {};
    }
    return eq.lit();
}

void add_assignment_literal(Linear_arithmetic* lra, Trail& trail, Models& models, Clause& out,
                            int var_ord)
{
    if (auto literal = ensure_assignment_literal(lra, trail, models, var_ord))
    {
        out.push_back(~literal.value()); // add inequality: var != current_value
    }
}

void add_bound_antecedents(Linear_arithmetic* lra, Trail& trail, Models& models, Clause& out,
                           Bound const& bound)
{
    out.push_back(~bound.reason().lit());

    for (auto var_ord : bound.reason().vars())
    {
        if (var_ord == bound.var())
        {
            continue;
        }

        bool covered_by_bound = std::any_of(bound.bounds().begin(), bound.bounds().end(),
                                            [&](auto const& other) { return other.var() == var_ord; });
        if (!covered_by_bound && models.owned().is_defined(var_ord))
        {
            if (auto literal = ensure_assignment_literal(lra, trail, models, var_ord))
            {
                out.push_back(~literal.value());
            }
        }
    }

    for (auto const& other : bound.bounds())
    {
        add_bound_antecedents(lra, trail, models, out, other);
    }
}

void deduplicate_clause(Clause& clause)
{
    Clause unique;
    unique.reserve(clause.size());
    for (auto lit : clause)
    {
        if (std::find(unique.begin(), unique.end(), lit) == unique.end())
        {
            unique.push_back(lit);
        }
    }
    clause = std::move(unique);
}

int clause_level(Trail const& trail, Clause const& clause)
{
    int level = 0;
    for (auto lit : clause)
    {
        level = std::max(level, trail.decision_level(lit.var()).value_or(0));
    }
    return level;
}

std::optional<Clause> mismatch_conflict(Linear_arithmetic* lra, Trail& trail, Models& models,
                                        Constraint const& cons)
{
    auto bool_val = eval(models.boolean(), cons.lit());
    auto theory_val = eval(models.owned(), cons);
    if (!bool_val.has_value() || !theory_val.has_value() || bool_val == theory_val)
    {
        return {};
    }

    auto current_branch = *bool_val ? cons : ~cons;
    auto conflict_lit = ~current_branch.lit();

    auto pivot_var = cons.vars().front();
    auto pivot_level =
        trail.decision_level(Variable{pivot_var, Variable::rational}).value_or(0);
    for (auto lra_var_ord : cons.vars())
    {
        auto level =
            trail.decision_level(Variable{lra_var_ord, Variable::rational}).value_or(0);
        if (level > pivot_level)
        {
            pivot_var = lra_var_ord;
            pivot_level = level;
        }
    }

    auto reduced_branch = [&]() -> std::optional<Constraint> {
        std::array<int, 1> vars{pivot_var};
        std::array<Rational, 1> coef{Rational{0}};
        auto rhs = current_branch.rhs();

        auto var_it = current_branch.vars().begin();
        auto coef_it = current_branch.coef().begin();
        for (; var_it != current_branch.vars().end(); ++var_it, ++coef_it)
        {
            if (*var_it == pivot_var)
            {
                coef.front() = *coef_it;
            }
            else
            {
                rhs -= *coef_it * models.owned().value(*var_it);
            }
        }

        if (coef.front() == 0)
        {
            return {};
        }

        auto reduced = lra->constraint(trail, vars, coef, current_branch.pred(), rhs);
        if (eval(models.owned(), reduced) != false)
        {
            reduced = ~reduced;
        }
        assert(eval(models.owned(), reduced) == false);
        return reduced;
    }();

    Clause conflict;
    conflict.reserve(static_cast<std::size_t>(cons.size()) + 1);
    conflict.push_back(conflict_lit);
    if (reduced_branch && reduced_branch->lit() != conflict_lit)
    {
        conflict.push_back(reduced_branch->lit());
    }

    for (auto lra_var_ord : cons.vars())
    {
        if (reduced_branch && lra_var_ord == pivot_var)
        {
            continue;
        }
        add_assignment_literal(lra, trail, models, conflict, lra_var_ord);
    }
    return conflict;
}

} // namespace

void Linear_arithmetic::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::rational)
    {
        bounds.resize(num_vars);
        watched.resize(num_vars);
        cached_values.resize(num_vars);
        occur.resize(num_vars);
    }
    else if (type == Variable::boolean)
    {
        constraints.resize(num_vars);
    }
}

void Linear_arithmetic::on_init(Database&, Trail&)
{
    reason_clauses.clear();
}

void Linear_arithmetic::on_restart(Database&, Trail&)
{
    reason_clauses.clear();
}

Clause* Linear_arithmetic::store_reason(Clause clause)
{
    deduplicate_clause(clause);
    reason_clauses.push_back(std::move(clause));
    return &reason_clauses.back();
}

bool Linear_arithmetic::is_effectively_decided(Models const& models, int lra_var_ord)
{
    if (models.owned().is_defined(lra_var_ord))
    {
        return false;
    }

    auto& bnds = bounds[lra_var_ord];
    if (auto lb = bnds.lower_bound(models))
    {
        if (auto ub = bnds.upper_bound(models))
        {
            return lb->value() == ub->value() && !lb->is_strict() && !ub->is_strict();
        }
    }

    if (options.prop_integer)
    {
        return count_integer_candidates(models, bnds, 2) == 1;
    }
    return false;
}

std::vector<Clause> Linear_arithmetic::propagate(Database&, Trail& trail)
{
    pending_conflict.reset();
    auto models = relevant_models(trail);

    // find relevant variables which have been assigned at current decision level
    std::vector<Variable> variables;
    std::vector<int> scan_vars;
    for (auto [var, _] : assigned(trail))
    {
        if (var.type() == Variable::rational ||
            (var.type() == Variable::boolean && !constraints[var.ord()].empty()))
        {
            variables.push_back(var);
            if (var.type() == Variable::rational)
            {
                scan_vars.push_back(var.ord());
            }
        }
    }

    for (auto var : variables)
    {
        if (var.type() == Variable::boolean)
        {
            auto cons = constraints[var.ord()];
            assert(!cons.empty());

            if (is_fully_assigned(models.owned(), cons))
            {
                if (auto conflict = mismatch_conflict(this, trail, models, cons))
                {
                    pending_conflict = std::move(*conflict);
                    break;
                }
            }
            else if (is_unit(models.owned(), cons))
            {
                unit(models, cons);
            }
        }
        else if (var.type() == Variable::rational)
        {
            replace_watch(trail, models, var.ord());
            if (pending_conflict)
            {
                break;
            }
        }
        else
        {
            assert(false);
        }
    }

    if (pending_conflict)
    {
        return {std::move(*pending_conflict)};
    }

    if (options.prop_bounds)
    {
        std::vector<int> changed_bounds;
        propagate_bounds(models, variables, scan_vars, changed_bounds);
        to_check.insert(to_check.end(), changed_bounds.begin(), changed_bounds.end());
        scan_vars.insert(scan_vars.end(), changed_bounds.begin(), changed_bounds.end());
    }
    else
    {
        auto const& changed = bounds.changed();
        to_check.insert(to_check.end(), changed.begin(), changed.end());
        scan_vars.insert(scan_vars.end(), changed.begin(), changed.end());
    }

    propagate_projected_bounds(trail, models, scan_vars);

    if (options.prop_unassigned && !scan_vars.empty())
    {
        std::sort(scan_vars.begin(), scan_vars.end());
        scan_vars.erase(std::unique(scan_vars.begin(), scan_vars.end()), scan_vars.end());
        propagate_unassigned(trail, models, scan_vars);
    }
    return finish(trail);
}

std::vector<Clause> Linear_arithmetic::check_model(Database&, Trail& trail)
{
    auto models = relevant_models(trail);
    for (auto cons : constraints)
    {
        if (cons.empty() || !models.boolean().is_defined(cons.lit().var().ord()) ||
            !is_fully_assigned(models.owned(), cons))
        {
            continue;
        }

        if (auto conflict = mismatch_conflict(this, trail, models, cons))
        {
            return {std::move(*conflict)};
        }
    }
    return {};
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
    auto out_coef_it = cons.coef().begin();
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

void Linear_arithmetic::replace_watch(Trail& trail, Models& models, int lra_var_ord)
{
    assert(models.owned().is_defined(lra_var_ord));

    auto& watchlist = watched[lra_var_ord];
    for (std::size_t i = 0; i < watchlist.size();)
    {
        if (pending_conflict)
        {
            return;
        }

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
                if (is_fully_assigned(models.owned(), cons))
                {
                    if (auto conflict = mismatch_conflict(this, trail, models, cons))
                    {
                        pending_conflict = std::move(*conflict);
                        return;
                    }
                }
                else // cons is unit
                {
                    assert(is_unit(models.owned(), cons));
                    unit(models, cons);
                }
            }
            else // cons is *not* on the trail
            {
                if (is_fully_assigned(models.owned(), cons))
                {
                    propagate(trail, models, cons);
                }
                else
                {
                    assert(is_unit(models.owned(), cons));
                }
            }
            ++i;
        }
    }
}

int Linear_arithmetic::decision_level(Trail const& trail, Constraint const& cons) const
{
    int level = trail.decision_level(cons.lit().var()).value_or(0);
    for (auto lra_var_ord : cons.vars())
    {
        Variable var{lra_var_ord, Variable::rational};
        level = std::max<int>(level, trail.decision_level(var).value_or(0));
    }
    return level;
}

Clause* Linear_arithmetic::explain_assigned_constraint(Trail& trail, Models& models,
                                                       Constraint const& cons)
{
    auto value = cons.eval(models.owned());
    Literal implied = value ? cons.lit() : ~cons.lit();

    Clause reason;
    reason.reserve(static_cast<std::size_t>(cons.size()) + 1);
    reason.push_back(implied);
    for (auto var_ord : cons.vars())
    {
        if (auto literal = ensure_assignment_literal(this, trail, models, var_ord))
        {
            reason.push_back(~literal.value());
        }
        else
        {
            return nullptr;
        }
    }
    return store_reason(std::move(reason));
}

Clause* Linear_arithmetic::explain_implied_constraint(Trail& trail, Models& models,
                                                      Constraint const& cons)
{
    if (cons.pred() == Order_predicate::eq)
    {
        return nullptr;
    }

    Clause reason;
    reason.reserve(static_cast<std::size_t>(cons.size()) * 4 + 1);
    reason.push_back(cons.lit());

    auto append_assignment = [&](Clause& out, int var_ord) -> bool {
        auto literal = ensure_assignment_literal(this, trail, models, var_ord);
        if (!literal)
        {
            return false;
        }
        out.push_back(~literal.value());
        return true;
    };

    auto bound = cons.rhs();
    auto [var_it, var_end] = cons.vars();
    auto coef_it = cons.coef().begin();
    for (; var_it != var_end; ++var_it, ++coef_it)
    {
        if (models.owned().is_defined(*var_it))
        {
            bound -= *coef_it * models.owned().value(*var_it);
            if (!append_assignment(reason, *var_it))
            {
                return nullptr;
            }
            continue;
        }

        Implied_value<Rational> const* bound_ptr = nullptr;
        if ((!cons.lit().is_negation() && *coef_it > 0) || (cons.lit().is_negation() && *coef_it < 0))
        {
            bound_ptr = bounds[*var_it].upper_bound(models);
        }
        else
        {
            bound_ptr = bounds[*var_it].lower_bound(models);
        }

        if (!bound_ptr)
        {
            return nullptr;
        }
        bound -= *coef_it * bound_ptr->value();
        add_bound_antecedents(this, trail, models, reason, *bound_ptr);
    }

    auto implied = cons.lit().is_negation() ? !cons.pred()(Rational{0}, bound)
                                            : cons.pred()(Rational{0}, bound);
    if (!implied)
    {
        return nullptr;
    }
    return store_reason(std::move(reason));
}

bool Linear_arithmetic::is_unit(Model<Rational> const& model, Constraint const& cons) const
{
    // Unit constraint will have exactly one watched variable assigned. The first two variables
    // in each constraint are the watched variables. Moreover, we move the unassigned variable
    // to the front in case one of the watched variables is assigned.
    if (cons.empty() || model.is_defined(cons.vars().front()))
    {
        return false;
    }
    return cons.size() == 1 || model.is_defined(cons.vars()[1]);
}

bool Linear_arithmetic::is_fully_assigned(Model<Rational> const& model,
                                          Constraint const& cons) const
{
    return cons.empty() ||
           std::all_of(cons.vars().begin(), cons.vars().end(),
                       [&](int v) { return model.is_defined(v); });
}

std::optional<Clause> Linear_arithmetic::check_bounds(Trail& trail, int var_ord)
{
    if (auto conflict = Bound_conflict_analysis{this, options.prop_integer}.analyze(trail, bounds, var_ord))
    {
        return conflict;
    }

    if (auto conflict = Inequality_conflict_analysis{this, options.prop_integer}.analyze(trail, bounds, var_ord))
    {
        return conflict;
    }
    return {}; // no conflict
}

void Linear_arithmetic::unit(Models const& models, Constraint const& cons) 
{ 
    bounds.update(models, cons); 
}

void Linear_arithmetic::propagate_bounds(Models const& models,
                                         std::vector<Variable> const& assigned_vars,
                                         std::vector<int> const& assigned_rationals,
                                         std::vector<int>& out_changed)
{
    out_changed.clear();

    std::vector<int> queue;
    queue.reserve(128);

    std::vector<char> in_queue(models.boolean().num_vars(), false);
    auto enqueue = [&](int bool_ord) {
        if (bool_ord < 0 || bool_ord >= static_cast<int>(in_queue.size()))
        {
            return;
        }
        if (!in_queue[bool_ord])
        {
            in_queue[bool_ord] = true;
            queue.push_back(bool_ord);
        }
    };

    // Seed with constraints whose boolean variables were just assigned.
    for (auto var : assigned_vars)
    {
        if (var.type() == Variable::boolean && !constraints[var.ord()].empty())
        {
            enqueue(var.ord());
        }
    }

    // Seed with constraints that mention newly assigned rational variables.
    for (auto var_ord : assigned_rationals)
    {
        for (auto cons : occur[var_ord])
        {
            auto bool_ord = cons.lit().var().ord();
            if (models.boolean().is_defined(bool_ord))
            {
                enqueue(bool_ord);
            }
        }
    }

    // Also seed with any bounds/inequalities derived before we got here (e.g., from unit
    // constraints while replacing watches).
    auto initial_changed = bounds.changed();
    out_changed.insert(out_changed.end(), initial_changed.begin(), initial_changed.end());
    for (auto var_ord : initial_changed)
    {
        for (auto cons : occur[var_ord])
        {
            auto bool_ord = cons.lit().var().ord();
            if (models.boolean().is_defined(bool_ord))
            {
                enqueue(bool_ord);
            }
        }
    }

    // Propagate FM deductions to a fixpoint (with a coarse budget cap).
    std::size_t index = 0;
    int budget = options.prop_integer ? 20000 : 2000;
    while (index < queue.size() && budget > 0)
    {
        auto bool_ord = queue[index++];
        in_queue[bool_ord] = false;
        --budget;

        if (!models.boolean().is_defined(bool_ord))
        {
            continue;
        }

        auto cons = constraint(bool_ord);
        if (cons.empty())
        {
            continue;
        }

        if (!models.boolean().value(bool_ord))
        {
            cons.negate();
        }
        assert(models.boolean().value(cons.lit().var().ord()) == !cons.lit().is_negation());
        bounds.deduce(models, cons);

        if (index == queue.size())
        {
            auto const& changed = bounds.changed();
            if (changed.empty())
            {
                continue;
            }

            out_changed.insert(out_changed.end(), changed.begin(), changed.end());
            for (auto var_ord : changed)
            {
                for (auto occ : occur[var_ord])
                {
                    auto occ_bool_ord = occ.lit().var().ord();
                    if (models.boolean().is_defined(occ_bool_ord))
                    {
                        enqueue(occ_bool_ord);
                    }
                }
            }
        }
    }

    // Drain any remaining bound updates.
    auto const& trailing_changed = bounds.changed();
    out_changed.insert(out_changed.end(), trailing_changed.begin(), trailing_changed.end());
}

void Linear_arithmetic::propagate_unassigned(Trail& trail, Models& models,
                                             std::vector<int> const& vars_to_check)
{
    if (vars_to_check.empty())
    {
        return;
    }

    std::unordered_set<int> seen;
    for (auto var_ord : vars_to_check)
    {
        for (auto cons : occur[var_ord])
        {
            auto bool_ord = cons.lit().var().ord();
            if (models.boolean().is_defined(bool_ord))
            {
                continue;
            }
            if (!seen.insert(bool_ord).second)
            {
                continue;
            }

            for (auto c : {cons, ~cons})
            {
                if (bounds.is_implied(models, c))
                {
                    models.boolean().set_value(bool_ord, !c.lit().is_negation());
                    trail.propagate(c.lit().var(), nullptr, trail.decision_level());
                    break;
                }
            }
        }
    }
}

std::vector<Clause> Linear_arithmetic::finish(Trail& trail)
{
    // check for conflict
    auto models = relevant_models(trail);
    std::unordered_set<int> checked;
    std::vector<Clause> result;
    for (auto var_ord : to_check)
    {
        auto [_, is_inserted] = checked.insert(var_ord);
        if (is_inserted)
        {
            if (auto conflict = check_bounds(trail, var_ord))
            {
                result.push_back(std::move(*conflict));
                if (!options.return_all_conflicts)
                {
                    break;
                }
            }
            else if (options.prop_rational && is_effectively_decided(models, var_ord))
            {
                decided.push_back(var_ord);
            }
        }
    }
    to_check.clear();
    return result;
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
    trail.propagate(cons.lit().var(), nullptr, dec_level);
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

std::optional<Rational> Linear_arithmetic::find_integer(Models const& models, Bounds_type& bounds)
{
    // check values 0, 1, -1, 2, -2, 3, -3, ..., length, -length
    auto check_around_zero = [&](Rational const& length) -> std::optional<Rational> {
        for (Rational value{0}; value <= length; value += 1)
        {
            if (bounds.is_allowed(models, value))
            {
                return value;
            }
            else if (bounds.is_allowed(models, -value))
            {
                return -value;
            }
        }
        return {};
    };

    auto lb = bounds.lower_bound(models);
    auto ub = bounds.upper_bound(models);
    if (!lb && !ub)
    {
        // examine all integers starting from 0
        Rational value{0};
        for (;;)
        {
            if (bounds.is_allowed(models, value))
            {
                return value;
            }
            else if (bounds.is_allowed(models, -value))
            {
                return -value;
            }
            value += 1;
        }
        return value;
    }
    else if (!lb)
    {
        Rational floor_ub = ub->value().floor();
        // try small integers in [-floor_ub, floor_ub] first if floor_ub is positive
        if (auto value = check_around_zero(floor_ub))
        {
            return value;
        }
        // try all other integers that are <= floor_ub
        Rational value = floor_ub > 0 ? -floor_ub : floor_ub;
        while (!bounds.is_allowed(models, value))
        {
            value -= 1;
        }
        return value;
    }
    else if (!ub)
    {
        Rational ceiling_lb = lb->value().ceil();
        // try small integers in [ceiling_lb, -ceiling_lb] first if ceiling_lb is negative
        if (auto value = check_around_zero(-ceiling_lb))
        {
            return value;
        }
        // try all other integers that are >= ceiling_lb
        Rational value = ceiling_lb < 0 ? -ceiling_lb : ceiling_lb;
        while (!bounds.is_allowed(models, value))
        {
            value += 1;
        }
        return value;
    }
    else // if (lb && ub)
    {
        assert(lb);
        assert(ub);

        if (lb->value() >= 0)
        {
            assert(ub->value() >= 0);
            for (Rational value = lb->value().ceil(); value <= ub->value(); value += 1)
            {
                if (bounds.is_allowed(models, value))
                {
                    return value;
                }
            }
            return {}; // none
        }
        else if (ub->value() <= 0)
        {
            assert(lb->value() <= 0);
            for (Rational value = ub->value().floor(); value >= lb->value(); value -= 1)
            {
                if (bounds.is_allowed(models, value))
                {
                    return value;
                }
            }
            return {}; // none
        }
        else // the interval of allowed values contains 0 in the middle
        {
            assert(lb->value() <= 0);
            assert(ub->value() >= 0);
            return check_around_zero(ub->value() > -lb->value() ? ub->value() : -lb->value());
        }
    }

    return {};
}

std::optional<Rational> Linear_arithmetic::guided_integer_value(Models const& models, int var_ord,
                                                                Rational const& preferred_value)
{
    auto& bnds = bounds[var_ord];
    Decision_interval interval;
    bool has_active_constraint = false;
    std::vector<Decision_interval> projected_intervals;
    std::vector<Rational> seeds;
    seeds.reserve(32);

    auto add_seed = [&](Rational const& value) {
        auto push = [&](Rational const& candidate) {
            if (std::ranges::find(seeds, candidate) == seeds.end())
            {
                seeds.push_back(candidate);
            }
        };

        if (value.isInteger())
        {
            push(value);
        }
        else
        {
            push(value.floor());
            push(value.ceil());
        }
    };

    add_seed(preferred_value);

    for (auto cons : occur[var_ord])
    {
        auto bool_ord = cons.lit().var().ord();
        if (!models.boolean().is_defined(bool_ord))
        {
            continue;
        }
        has_active_constraint = true;

        if (!models.boolean().value(bool_ord))
        {
            cons.negate();
        }
        auto projected = project_interval(cons, var_ord, [&](int other_var_ord) {
            return models.owned().is_defined(other_var_ord)
                       ? models.owned().value(other_var_ord)
                       : cached_values.is_defined(other_var_ord) ? cached_values.value(other_var_ord)
                                                                 : Rational{0};
        });
        if (!projected)
        {
            continue;
        }
        projected_intervals.push_back(*projected);
        merge_interval(interval, *projected);
        if (projected->lb)
        {
            add_seed(lower_seed(*projected->lb, projected->lb_strict));
        }
        if (projected->ub)
        {
            add_seed(upper_seed(*projected->ub, projected->ub_strict));
        }
        if (projected->lb && projected->ub)
        {
            add_seed((*projected->lb + *projected->ub) / Rational{2});
        }
    }

    if (!has_active_constraint)
    {
        return {};
    }

    if (auto lb = bnds.lower_bound(models))
    {
        add_seed(lower_seed(lb->value(), lb->is_strict()));
    }
    if (auto ub = bnds.upper_bound(models))
    {
        add_seed(upper_seed(ub->value(), ub->is_strict()));
    }

    struct Candidate_score {
        int violated;
        Rational preferred_distance;
        Rational zero_distance;
    };

    auto better = [](Candidate_score const& lhs, Candidate_score const& rhs) {
        if (lhs.violated != rhs.violated)
        {
            return lhs.violated < rhs.violated;
        }
        if (lhs.preferred_distance != rhs.preferred_distance)
        {
            return lhs.preferred_distance < rhs.preferred_distance;
        }
        return lhs.zero_distance < rhs.zero_distance;
    };

    std::optional<Rational> best;
    std::optional<Candidate_score> best_score;
    std::vector<Rational> seen_candidates;
    seen_candidates.reserve(seeds.size() * 8);

    auto try_candidate = [&](Rational const& candidate) {
        if (std::ranges::find(seen_candidates, candidate) != seen_candidates.end())
        {
            return;
        }
        seen_candidates.push_back(candidate);
        if (!bnds.is_allowed(models, candidate))
        {
            return;
        }

        int violated = 0;
        for (auto const& projected : projected_intervals)
        {
            violated += !interval_allows(projected, candidate);
        }

        Candidate_score score{violated, distance(candidate, preferred_value),
                              distance(candidate, Rational{0})};
        if (!best_score || better(score, *best_score))
        {
            best = candidate;
            best_score = score;
        }
    };

    constexpr int radius_limit = 16;
    for (int delta = 0; delta <= radius_limit; ++delta)
    {
        Rational const step{delta};
        for (auto const& seed : seeds)
        {
            try_candidate(seed + step);
            if (delta != 0)
            {
                try_candidate(seed - step);
            }
        }
    }

    if (best)
    {
        return best;
    }

    return choose_candidate(interval, preferred_value, [&](Rational const& candidate) {
        return interval_allows(interval, candidate) && bnds.is_allowed(models, candidate);
    });
}

void Linear_arithmetic::repair_integer_model(Models const& models, int focus_var)
{
    if (!options.prop_integer || focus_var < 0 ||
        focus_var >= static_cast<int>(occur.size()))
    {
        return;
    }

    auto seed_value = [&](int var_ord) -> Rational {
        if (models.owned().is_defined(var_ord))
        {
            return models.owned().value(var_ord);
        }
        if (cached_values.is_defined(var_ord))
        {
            return cached_values.value(var_ord);
        }

        auto& bnds = bounds[var_ord];
        if (bnds.is_allowed(models, Rational{0}))
        {
            cached_values.set_value(var_ord, Rational{0});
            return Rational{0};
        }

        if (auto value = find_integer(models, bnds))
        {
            cached_values.set_value(var_ord, *value);
            return *value;
        }

        cached_values.set_value(var_ord, Rational{0});
        return Rational{0};
    };

    auto shadow_value = [&](int var_ord) -> Rational {
        return models.owned().is_defined(var_ord) ? models.owned().value(var_ord) : seed_value(var_ord);
    };

    std::vector<int> queue;
    queue.reserve(32);
    std::vector<char> in_queue(cached_values.num_vars(), false);
    auto enqueue = [&](int var_ord) {
        if (var_ord < 0 || var_ord >= static_cast<int>(in_queue.size()))
        {
            return;
        }
        if (!in_queue[var_ord] && !models.owned().is_defined(var_ord))
        {
            in_queue[var_ord] = true;
            queue.push_back(var_ord);
        }
    };

    enqueue(focus_var);
    for (auto cons : occur[focus_var])
    {
        auto bool_ord = cons.lit().var().ord();
        if (!models.boolean().is_defined(bool_ord))
        {
            continue;
        }
        for (auto var_ord : cons.vars())
        {
            enqueue(var_ord);
        }
    }

    std::size_t index = 0;
    int budget = std::min<int>(256, std::max<int>(32, static_cast<int>(occur[focus_var].size()) * 8));
    while (index < queue.size() && budget-- > 0)
    {
        auto var_ord = queue[index++];
        in_queue[var_ord] = false;

        for (auto cons : occur[var_ord])
        {
            auto bool_ord = cons.lit().var().ord();
            if (!models.boolean().is_defined(bool_ord))
            {
                continue;
            }

            if (!models.boolean().value(bool_ord))
            {
                cons.negate();
            }

            if (satisfies(cons, shadow_value))
            {
                continue;
            }

            std::vector<int> candidates;
            candidates.reserve(cons.size());
            if (!models.owned().is_defined(focus_var) &&
                std::find(cons.vars().begin(), cons.vars().end(), focus_var) != cons.vars().end())
            {
                candidates.push_back(focus_var);
            }
            for (auto other_var_ord : cons.vars())
            {
                if (!models.owned().is_defined(other_var_ord) &&
                    std::ranges::find(candidates, other_var_ord) == candidates.end())
                {
                    candidates.push_back(other_var_ord);
                }
            }

            bool repaired = false;
            for (auto pivot_var : candidates)
            {
                auto projected = project_interval(cons, pivot_var, [&](int other_var_ord) {
                    return shadow_value(other_var_ord);
                });
                if (!projected)
                {
                    continue;
                }

                auto preferred =
                    cached_values.is_defined(pivot_var) ? cached_values.value(pivot_var) : Rational{0};
                auto candidate = choose_candidate(*projected, preferred, [&](Rational const& value) {
                    return interval_allows(*projected, value) &&
                           bounds[pivot_var].is_allowed(models, value);
                });
                if (!candidate)
                {
                    continue;
                }

                if (!cached_values.is_defined(pivot_var) ||
                    cached_values.value(pivot_var) != *candidate)
                {
                    cached_values.set_value(pivot_var, *candidate);
                }

                if (satisfies(cons, shadow_value))
                {
                    enqueue(pivot_var);
                    repaired = true;
                    break;
                }
            }

            if (repaired)
            {
                continue;
            }
        }
    }
}

int Linear_arithmetic::implied_level(Trail const& trail,
                                     Implied_value<Rational> const& bound) const
{
    int level = trail.decision_level(bound.reason().lit().var()).value_or(0);
    for (auto var_ord : bound.reason().vars())
    {
        if (var_ord != bound.var())
        {
            level = std::max<int>(level,
                                  trail.decision_level(Variable{var_ord, Variable::rational})
                                      .value_or(0));
        }
    }
    for (auto const& other : bound.bounds())
    {
        level = std::max<int>(level, implied_level(trail, other));
    }
    return level;
}

void Linear_arithmetic::propagate_projected_bounds(Trail& trail, Models& models,
                                                   std::vector<int> const& vars_to_check)
{
    if (vars_to_check.empty())
    {
        return;
    }

    std::unordered_set<int> seen;
    auto propagate_literal = [&](Constraint const& cons, int level, Clause* reason) {
        auto bool_ord = cons.lit().var().ord();
        auto current = eval(models.boolean(), cons.lit());
        if (current.has_value())
        {
            return;
        }

        models.boolean().set_value(bool_ord, !cons.lit().is_negation());
        trail.propagate(cons.lit().var(), reason, reason ? clause_level(trail, *reason) : level);
    };

    auto make_equality = [&](int var_ord, Rational const& value) {
        std::array<int, 1> vars{var_ord};
        std::array<Rational, 1> coef{Rational{1}};
        return constraint(trail, vars, coef, Order_predicate::eq, value);
    };
    auto make_upper = [&](int var_ord, Rational const& value, bool strict) {
        std::array<int, 1> vars{var_ord};
        std::array<Rational, 1> coef{Rational{1}};
        return constraint(trail, vars, coef, strict ? Order_predicate::lt : Order_predicate::leq,
                          value);
    };
    auto make_lower = [&](int var_ord, Rational const& value, bool strict) {
        std::array<int, 1> vars{var_ord};
        std::array<Rational, 1> coef{Rational{-1}};
        return constraint(trail, vars, coef, strict ? Order_predicate::lt : Order_predicate::leq,
                          -value);
    };

    for (auto var_ord : vars_to_check)
    {
        if (!seen.insert(var_ord).second || models.owned().is_defined(var_ord))
        {
            continue;
        }

        auto& bnds = bounds[var_ord];
        auto lb = bnds.lower_bound(models);
        auto ub = bnds.upper_bound(models);
        if (lb && ub && lb->value() == ub->value() && !lb->is_strict() && !ub->is_strict())
        {
            auto eq = make_equality(var_ord, lb->value());
            propagate_literal(eq, std::max(implied_level(trail, *lb), implied_level(trail, *ub)),
                              nullptr);
            continue;
        }

        if (lb)
        {
            auto lower = make_lower(var_ord, lb->value(), lb->is_strict());
            propagate_literal(lower, implied_level(trail, *lb), nullptr);
        }
        if (ub)
        {
            auto upper = make_upper(var_ord, ub->value(), ub->is_strict());
            propagate_literal(upper, implied_level(trail, *ub), nullptr);
        }
    }
}

void Linear_arithmetic::decide(Database&, Trail& trail, Variable var)
{
    if (var.type() != Variable::rational)
    {
        return;
    }

    auto models = relevant_models(trail);
    auto& bnds = bounds[var.ord()];
    if (options.prop_integer)
    {
        repair_integer_model(models, var.ord());
    }

    Rational value =
        cached_values.is_defined(var.ord()) ? cached_values.value(var.ord()) : Rational{0};
    if (options.prop_integer)
    {
        if (auto guided = guided_integer_value(models, var.ord(), value))
        {
            value = guided.value();
        }
    }
    if (!bnds.is_allowed(models, value))
    {
        if (auto int_value = find_integer(models, bnds))
        {
            value = int_value.value();
        }
        else // there is no suitable integer value
        {
            // LRA has to be chosen, otherwise a conflict should be detected
            assert(!options.prop_integer);
            assert(bnds.lower_bound(models) != nullptr);
            assert(bnds.upper_bound(models) != nullptr);

            auto const& lb = bnds.lower_bound(models)->value();
            auto const& ub = bnds.upper_bound(models)->value();

            value = std::move(ub);
            while (!bnds.is_allowed(models, value))
            {
                value = (value + lb) / Rational{2};
            }
        }
    }

    // decide the value
    cached_values.set_value(var.ord(), value);
    assert(bnds.is_allowed(models, value));
    models.owned().set_value(var.ord(), value);
    trail.decide(var);
}

void Linear_arithmetic::check_bounds_consistency([[maybe_unused]] Trail const& trail,
                                                 Models const& models)
{
    std::vector<std::optional<Rational>> ub;
    std::vector<std::optional<Rational>> lb;
    std::vector<Constraint> ub_reason;
    std::vector<Constraint> lb_reason;
    ub.resize(models.owned().num_vars(), {});
    lb.resize(models.owned().num_vars(), {});
    ub_reason.resize(models.owned().num_vars());
    lb_reason.resize(models.owned().num_vars());

    // compute actual bounds
    for (auto c : constraints)
    {
        if (c.empty() || !models.boolean().is_defined(c.lit().var().ord()))
        {
            continue;
        }

        auto cons = models.boolean().value(c.lit().var().ord()) == !c.lit().is_negation() ? c : ~c;
        bool unit = !models.owned().is_defined(cons.vars().front()) &&
                    std::all_of(cons.vars().begin() + 1, cons.vars().end(),
                                [&](auto ord) { return models.owned().is_defined(ord); });
        if (unit)
        {
            auto var = cons.vars().front();
            auto bound = cons.implied_value(models.owned()) / cons.coef().front();
            if (bounds.implies_upper_bound(cons))
            {
                if (!ub[var] || bound < *ub[var])
                {
                    ub[var] = bound;
                    ub_reason[var] = cons;
                }
            }

            if (bounds.implies_lower_bound(cons))
            {
                if (!lb[var] || bound > *lb[var])
                {
                    lb[var] = bound;
                    lb_reason[var] = cons;
                }
            }
        }
    }

    // check consistency with the bounds object
    for (int var_ord = 0; var_ord < static_cast<int>(ub.size()); ++var_ord)
    {
        if (models.owned().is_defined(var_ord))
        {
            continue;
        }

        auto& bnds = bounds[var_ord];
        if ([[maybe_unused]] auto lower_bound = bnds.lower_bound(models))
        {
            assert(!lb[var_ord] || lower_bound->value() >= *lb[var_ord]);
        }

        if ([[maybe_unused]] auto upper_bound = bnds.upper_bound(models))
        {
            assert(!ub[var_ord] || upper_bound->value() <= *ub[var_ord]);
        }
    }
}

void Linear_arithmetic::check_watch_consistency([[maybe_unused]] Models const& models)
{
    for (auto cons : constraints)
    {
        if (cons.empty())
        {
            continue;
        }

        // the first variable is assigned => all variables are assigned
        assert(!models.owned().is_defined(cons.vars().front()) ||
               std::all_of(cons.vars().begin(), cons.vars().end(),
                           [&](auto var) { return models.owned().is_defined(var); }));
        if (cons.size() > 1)
        {
            // the second variable is assigned => the constraint is unit
            assert(!models.owned().is_defined(cons.vars()[1]) ||
                   std::all_of(cons.vars().begin() + 2, cons.vars().end(),
                               [&](auto var) { return models.owned().is_defined(var); }));
        }

        for ([[maybe_unused]] auto var : cons.vars() | std::views::take(2))
        {
            assert(std::find_if(watched[var].begin(), watched[var].end(), [cons](auto& watch) {
                       return watch.constraint.lit().var() == cons.lit().var();
                   }) != watched[var].end());
        }
    }
}

} // namespace yaga
