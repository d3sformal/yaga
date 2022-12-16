#include "Subsumption.h"

namespace perun {

void Subsumption::on_variable_resize(Variable::Type type, int num_vars)
{
    if (type == Variable::boolean)
    {
        occur_.resize(num_vars);
        bitset_.resize(num_vars);
    }
}

void Subsumption::on_conflict_clause(Database&, Trail& trail, Clause& conflict)
{
    const auto& model = trail.model<bool>(Variable::boolean);

    conflict.erase(std::remove_if(conflict.begin(), conflict.end(), [&](auto lit) 
    {
        if (is_true(model, lit.negate()))
        {
            auto reason = trail.reason(lit.var());
            return reason && selfsubsumes(*reason, conflict, lit.negate());
        }
        return false;
    }), conflict.end());
}

void Subsumption::on_restart(Database& db, Trail&)
{
    remove_subsumed(db.learned());
}

void Subsumption::index(const std::deque<Clause>& clauses)
{
    for (auto& list : occur_)
    {
        list.clear();
    }

    for (const auto& clause : clauses)
    {
        auto clause_ptr = make_proxy(&clause);

        for (auto lit : clause)
        {
            occur_[lit].emplace_back(clause_ptr);
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

    bitset_.assign(false);
    for (auto lit : *second)
    {
        bitset_[lit] = true;
    }

    for (auto lit : *first)
    {
        if (!bitset_[lit])
        {
            return false;
        }
    }
    return true;
}

bool Subsumption::selfsubsumes(const Clause& first, const Clause& second, Literal lit)
{
    assert(std::find(first.begin(), first.end(), lit) != first.end());
    assert(std::find(second.begin(), second.end(), lit.negate()) != second.end());

    if (first.size() > second.size())
    {
        return false;
    }

    bitset_.assign(false);
    bitset_[lit] = true;
    for (auto l : second)
    {
        bitset_[l] = true;
    }

    for (auto l : first)
    {
        if (!bitset_[l])
        {
            return false;
        }
    }
    return true;
}

void Subsumption::remove_subsumed(Subsumption::Clause_ptr clause, std::unordered_set<const Clause*>& removed)
{
    if (clause->empty())
    {
        return;
    }

    // find literal in clause with the shortest occur list
    Literal best_lit = *clause->begin();
    std::size_t best_size = occur_[best_lit].size();
    for (auto it = clause->begin() + 1; it != clause->end(); ++it)
    {
        if (occur_[*it].size() < best_size)
        {
            best_lit = *it;
            best_size = occur_[*it].size();
        }
    }

    // remove subsumed clauses
    auto& intersection = occur_[best_lit];
    auto end = std::partition(intersection.begin(), intersection.end(), [&](auto other_ptr) 
    {
        return other_ptr == clause || !subsumes(clause, other_ptr);
    });

    for (auto it = end; it != intersection.end(); ++it)
    {
        removed.insert(&*(*it)); // convert the Clause_ptr proxy to an actual pointer
    }
    intersection.erase(end, intersection.end());
}

void Subsumption::remove_subsumed(std::deque<Clause>& clauses)
{
    index(clauses);

    // find subsumed clauses
    std::unordered_set<const Clause*> removed;
    for (const auto& clause : clauses)
    {
        remove_subsumed(make_proxy(&clause), removed);
    }

    // remove them from the list
    clauses.erase(std::remove_if(clauses.begin(), clauses.end(), [&](const auto& clause) {
        return removed.contains(&clause);
    }), clauses.end());
}

}