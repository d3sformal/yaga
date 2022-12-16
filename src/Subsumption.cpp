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
    auto end = occur_[best_lit].begin();
    for (auto other_clause_ptr : occur_[best_lit])
    {
        if (other_clause_ptr != clause && subsumes(clause, other_clause_ptr))
        {
            // convert the Clause_ptr proxy to an actual pointer
            removed.insert(&*other_clause_ptr); 
        }
        else // keep other clause in the adjacency list
        {
            *end = other_clause_ptr;
            ++end;
        }
    }
    occur_[best_lit].erase(end, occur_[best_lit].end());
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