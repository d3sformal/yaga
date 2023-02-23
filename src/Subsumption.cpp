#include "Subsumption.h"

namespace perun {

void Subsumption::minimize(Trail const& trail, Clause& clause)
{
    auto const& model = trail.model<bool>(Variable::boolean);

    auto is_redundant = [&](auto lit) {
        if (eval(model, lit.negate()) == true)
        {
            auto reason = trail.reason(lit.var());
            return reason && selfsubsumes(*reason, clause, lit.negate());
        }
        return false;
    };

    clause.erase(std::remove_if(clause.begin(), clause.end(), is_redundant), clause.end());
}

void Subsumption::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::boolean)
    {
        occur.resize(num_vars);
        lit_bitset.resize(num_vars);
    }
}

void Subsumption::on_restart(Database& db, Trail&) { remove_subsumed(db); }

bool Subsumption::subsumes(Subsumption::Clause_ptr first, Subsumption::Clause_ptr second)
{
    if ((first.sig() & ~second.sig()) != 0)
    {
        return false;
    }

    if (first->size() >= second->size())
    {
        return false;
    }

    lit_bitset.assign(false);
    for (auto lit : *second)
    {
        lit_bitset[lit] = true;
    }

    for (auto lit : *first)
    {
        if (!lit_bitset[lit])
        {
            return false;
        }
    }
    return true;
}

bool Subsumption::selfsubsumes(Clause const& first, Clause const& second, Literal lit)
{
    assert(std::find(first.begin(), first.end(), lit) != first.end());
    assert(std::find(second.begin(), second.end(), lit.negate()) != second.end());

    if (first.size() > second.size())
    {
        return false;
    }

    lit_bitset.assign(false);
    lit_bitset[lit] = true;
    for (auto l : second)
    {
        lit_bitset[l] = true;
    }

    for (auto l : first)
    {
        if (!lit_bitset[l])
        {
            return false;
        }
    }
    return true;
}

void Subsumption::index(Clause_iterator it, Clause_iterator end)
{
    for (auto& list : occur)
    {
        list.clear();
    }

    for (; it != end; ++it)
    {
        auto& clause = *it;
        auto clause_ptr = make_proxy(&clause);

        for (auto lit : clause)
        {
            occur[lit].emplace_back(clause_ptr);
        }
    }
}

void Subsumption::remove_subsumed(Subsumption::Clause_ptr clause)
{
    if (clause->empty())
    {
        return;
    }

    // find literal in clause with the shortest occur list
    Literal best_lit = *clause->begin();
    std::size_t best_size = occur[best_lit].size();
    for (auto it = clause->begin() + 1; it != clause->end(); ++it)
    {
        if (occur[*it].size() < best_size)
        {
            best_lit = *it;
            best_size = occur[*it].size();
        }
    }

    // remove subsumed clauses
    for (auto other_ptr : occur[best_lit])
    {
        if (other_ptr != clause && subsumes(clause, other_ptr))
        {
            other_ptr->clear();
        }
    }
}

void Subsumption::remove_subsumed(Database& db)
{
    auto const old_end = db.learned().begin() + old_size;

    // find old clauses subsumed by a new clause
    index(db.learned().begin(), old_end);
    for (auto it = old_end; it != db.learned().end(); ++it)
    {
        remove_subsumed(make_proxy(&*it));
    }

    // find new clauses subsumed by any clause (old or new)
    index(old_end, db.learned().end());
    for (auto& clause : db.learned())
    {
        remove_subsumed(make_proxy(&clause));
    }

    // remove all subsumed clauses from the database
    db.learned().erase(std::remove_if(db.learned().begin(), db.learned().end(),
                                      [](auto const& clause) { return clause.empty(); }),
                       db.learned().end());
    old_size = db.learned().size();
}

} // namespace perun