#include "Bool_theory.h"

namespace perun {

void Bool_theory::decide(Database&, Trail& trail, Variable var)
{
    if (var.type() == Variable::boolean)
    {
        auto& model = trail.model<bool>(Variable::boolean);
        model.set_value(var.ord(), true);
        trail.decide(var);
    }
}

void Bool_theory::on_learned_clause(Database&, Trail&, Clause* learned)
{
    // initialize watched literals in the learned clause
    watched_[(*learned)[0]].emplace_back(learned);
    if (learned->size() > 1)
    {
        watched_[(*learned)[1]].emplace_back(learned);
    }
}

std::optional<Clause> Bool_theory::initialize(Database& db, Trail& trail)
{
    const auto& model = trail.model<bool>(Variable::boolean);
    
    // allocate space for new variables if necessary
    watched_.resize(model.num_vars());

    if (trail.empty()) // initialize watch lists
    {
        // clear watch lists
        for (auto& list : watched_)
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
                    watched_[clause[0]].emplace_back(Watched_clause{&clause});
                    propagate_.push_back({clause[0], &clause});
                }
                else // non-unit clause
                {
                    watched_[clause[0]].emplace_back(&clause);
                    watched_[clause[1]].emplace_back(&clause);
                }
            }
        }
    }

    // propagate assigned variables
    for (auto [var, reason] : trail.assigned(trail.decision_level()))
    {
        if (var.type() == Variable::boolean)
        {
            auto lit = model.value(var.ord()) ? Literal{var.ord()} : Literal{var.ord()}.negate();
            propagate_.push_back({lit, reason});
        }
    }

    return {};
}

std::optional<Clause> Bool_theory::propagate(Database& db, Trail& trail) 
{
    propagate_.clear();

    auto& model = trail.model<bool>(Variable::boolean);
    auto conflict = initialize(db, trail);

    while (!conflict && !propagate_.empty())
    {
        auto [lit, reason] = propagate_.back();
        propagate_.pop_back();

        // propagate the literal if necessary
        if (reason != nullptr && !model.is_defined(lit.var().ord()))
        {
            model.set_value(lit.var().ord(), !lit.is_negation());
            trail.propagate(lit.var(), reason, trail.decision_level());
        }
        assert(eval(model, lit) == true);

        conflict = falsified(model, lit.negate());
    }
    return conflict;
}

bool Bool_theory::replace_second_watch(const Model<bool>& model, Watched_clause& watch)
{
    auto& clause = *watch.clause;

    assert(clause.size() >= 2);
    assert(eval(model, clause[1]) == false);
    assert(eval(model, clause[0]) != true);

    if (clause.size() > 2)
    {
        assert(2 <= watch.index && watch.index < static_cast<int>(clause.size()));
        const auto end = watch.index;
        do
        {
            // check if the next literal is non-falsified
            if (eval(model, clause[watch.index]) != false)
            {
                std::swap(clause[1], clause[watch.index]);
                watched_[clause[1]].push_back(watch);
                return true;
            }

            // move to the next literal
            if (++watch.index >= static_cast<int>(clause.size()))
            {
                watch.index = 2; // skip the watched literals
            }
        }
        while (watch.index != end);
    }
    return false;
}

std::optional<Clause> Bool_theory::falsified(const Model<bool>& model, Literal falsified_lit)
{
    assert(eval(model, falsified_lit) == false);

    auto& watchlist = watched_[falsified_lit];
    for (std::size_t i = 0; i < watchlist.size();)
    {
        auto& watch = watchlist[i];
        auto& clause = *watch.clause;

        assert(clause.size() >= 1);
        if (clause.size() == 1)
        {
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
        else // there is no other non-falsified literal in clause
        {
            if (eval(model, clause[0]) == false) // if the clause is false
            {
                return clause;
            }
            propagate_.push_back({clause[0], &clause});
            ++i;
        }
    }
    return {};
}

}