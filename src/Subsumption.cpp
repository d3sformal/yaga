#include "Subsumption.h"

namespace perun {

void Subsumption::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::boolean)
    {
        occur.resize(num_vars);
        lit_bitset.resize(num_vars);
    }
}

void Subsumption::on_conflict_derived(Database&, Trail& trail, Clause& conflict)
{
    auto const& model = trail.model<bool>(Variable::boolean);

    auto is_redundant = [&](auto lit) {
        if (eval(model, lit.negate()) == true)
        {
            auto reason = trail.reason(lit.var());
            return reason && selfsubsumes(*reason, conflict, lit.negate());
        }
        return false;
    };

    conflict.erase(std::remove_if(conflict.begin(), conflict.end(), is_redundant), conflict.end());
}

void Subsumption::on_restart(Database& db, Trail&) { remove_subsumed(db); }

void Subsumption::index(std::deque<Clause>& clauses)
{
    for (auto& list : occur)
    {
        list.clear();
    }

    for (auto& clause : clauses)
    {
        auto clause_ptr = make_proxy(&clause);

        for (auto lit : clause)
        {
            occur[lit].emplace_back(clause_ptr);
        }
    }
}

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
    index(db.learned());

    // find subsumed clauses
    for (auto& clause : db.learned())
    {
        remove_subsumed(make_proxy(&clause));
    }

    // remove them from the list
    db.learned().erase(std::remove_if(db.learned().begin(), db.learned().end(),
                                      [](auto const& clause) { return clause.empty(); }),
                       db.learned().end());
}

} // namespace perun