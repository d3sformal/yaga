#include "Bool_theory.h"

namespace yaga {

void Bool_theory::decide(Database&, Trail& trail, Variable var)
{
    if (var.type() == Variable::boolean)
    {
        auto& model = trail.model<bool>(Variable::boolean);
        model.set_value(var.ord(), true);
        trail.decide(var);
    }
}

void Bool_theory::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::boolean)
    {
        watched.resize(num_vars);
    }
}

void Bool_theory::on_learned_clause(Database& db, Trail&, Clause const& learned)
{
    // find the learned clause in database (should be exactly one comparison since learned clauses
    // are added to the back)
    auto it = std::find_if(
        db.learned().rbegin(), db.learned().rend(),
        [learned_ptr = &learned](auto const& clause) { return &clause == learned_ptr; });
    assert(it != db.learned().rend());

    // watch the first two literals in the learned clause
    watched[learned[0]].emplace_back(&*it);
    if (learned.size() > 1)
    {
        watched[learned[1]].emplace_back(&*it);
    }
}

void Bool_theory::initialize(Database& db, Trail& trail)
{
    auto const& model = trail.model<bool>(Variable::boolean);

    // allocate space for new variables if necessary
    watched.resize(model.num_vars());

    if (trail.empty()) // initialize watch lists
    {
        // clear watch lists
        for (auto& list : watched)
        {
            list.clear();
        }

        // initialize watched literals
        auto& asserted = db.asserted();
        auto& learned = db.learned();
        for (auto clause_list : {&asserted, &learned})
        {
            for (auto& clause : *clause_list)
            {
                if (clause.size() == 1) // propagate unit clauses
                {
                    watched[clause[0]].emplace_back(Watched_clause{&clause});
                    satisfied.push_back({.lit = clause[0], .reason = &clause});
                }
                else // non-unit clause
                {
                    watched[clause[0]].emplace_back(&clause);
                    watched[clause[1]].emplace_back(&clause);
                }
            }
        }
    }

    // propagate assigned variables
    for (auto [var, reason] : assigned(trail))
    {
        if (var.type() == Variable::boolean)
        {
            auto lit = model.value(var.ord()) ? Literal{var.ord()} : ~Literal{var.ord()};
            satisfied.push_back({.lit = lit, .reason = reason});
        }
    }
}

std::vector<Clause> Bool_theory::propagate(Database& db, Trail& trail)
{
    satisfied.clear();

    auto& model = trail.model<bool>(Variable::boolean);
    initialize(db, trail);

    std::vector<Clause> conflicts;
    while (conflicts.empty() && !satisfied.empty())
    {
        auto [lit, reason] = satisfied.back();
        satisfied.pop_back();

        // propagate the literal if necessary
        if (reason != nullptr && !model.is_defined(lit.var().ord()))
        {
            model.set_value(lit.var().ord(), !lit.is_negation());
            trail.propagate(lit.var(), reason, trail.decision_level());
        }
        assert(eval(model, lit) == true);
        // reason clause is a unit clause which implies lit
        assert(reason == nullptr || std::all_of(reason->begin(), reason->end(), [&](auto other_lit) {
            return other_lit == lit || eval(model, other_lit) == false;
        }));

        if (auto conflict = falsified(trail, model, ~lit))
        {
            conflicts.push_back(std::move(conflict.value()));
        }
    }

    return conflicts;
}

bool Bool_theory::replace_second_watch(Model<bool> const& model, Watched_clause& watch)
{
    auto& clause = *watch.clause;

    assert(clause.size() >= 2);
    assert(eval(model, clause[1]) == false);

    if (clause.size() > 2)
    {
        assert(2 <= watch.index && watch.index < static_cast<int>(clause.size()));
        auto const end = watch.index;
        do
        {
            // check if the next literal is non-falsified
            auto value = eval(model, clause[watch.index]);
            if (value != false)
            {
                std::swap(clause[1], clause[watch.index]);
                watched[clause[1]].push_back(watch);
                return true;
            }

            // move to the next literal
            if (++watch.index >= static_cast<int>(clause.size()))
            {
                watch.index = 2; // skip the watched literals
            }
        } while (watch.index != end);
    }
    return false;
}

std::optional<Clause> 
Bool_theory::falsified([[maybe_unused]] Trail const& trail, Model<bool> const& model, Literal falsified_lit)
{
    assert(eval(model, falsified_lit) == false);

    auto& watchlist = watched[falsified_lit];
    for (std::size_t i = 0; i < watchlist.size();)
    {
        auto& watch = watchlist[i];
        auto& clause = *watch.clause;

        assert(clause.size() >= 1);
        if (clause.size() == 1)
        {
            assert(eval(model, clause) == false);
            return clause; // the clause has just become empty
        }

        // move falsified literal to index 1
        if (clause[0] == falsified_lit)
        {
            std::swap(clause[0], clause[1]);
        }
        assert(clause[1] == falsified_lit);

        // skip satisfied clauses
        if (eval(model, clause[0]) == true)
        {
            ++i;
            continue;
        }

        if (replace_second_watch(model, watch))
        {
            std::swap(watch, watchlist.back());
            watchlist.pop_back();
        }
        else // `clause` is unit or false
        {
            ++i;

            // the second watch has the highest decision level
            assert(std::max_element(clause.begin() + 1, clause.end(), [&](auto lhs, auto rhs) {
                return *trail.decision_level(lhs.var()) < *trail.decision_level(rhs.var());
            }) == clause.begin() + 1);

            if (eval(model, clause[0]) == false) // if the clause is false
            {
                assert(eval(model, clause) == false);
                return clause;
            }
            
            // the clause is unit
            assert(!eval(model, clause[0]).has_value());
            assert(std::all_of(clause.begin() + 1, clause.end(), [&](auto lit) {
                return eval(model, lit) == false;
            }));
            assert(clause.size() > 1);
            satisfied.push_back({.lit = clause[0], .reason = &clause});
        }
    }
    return {};
}

} // namespace yaga