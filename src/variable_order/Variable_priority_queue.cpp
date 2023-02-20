#include "Variable_priority_queue.h"

namespace perun {

void Variable_priority_queue::push(Variable var, float score)
{
    if (position.size() <= var.type())
    {
        position.resize(var.type() + 1);
    }

    if (position[var.type()].size() <= static_cast<std::size_t>(var.ord()))
    {
        position[var.type()].resize(var.ord() + 1, missing);
    }
    assert(position[var.type()][var.ord()] == missing);

    // add the variable to the priority queue
    position[var.type()][var.ord()] = pq.size();
    fix_up(pq.insert(pq.end(), {var, score}));
}

void Variable_priority_queue::pop()
{
    assert(!empty());

    auto var = pq.front().first;

    swap(pq.begin(), pq.begin() + (pq.size() - 1));
    pq.pop_back();

    if (!pq.empty())
    {
        fix_down(pq.begin());
    }

    position[var.type()][var.ord()] = missing;
}

void Variable_priority_queue::update(Variable var, float score)
{
    auto it = find(var);
    if (it == pq.end())
    {
        return;
    }

    assert(it != pq.end());
    assert(it->second <= score);
    auto old_score = it->second;
    it->second = score;

    if (old_score <= score)
    {
        fix_up(it);
    }
    else // old_score > score
    {
        fix_down(it);
    }
}

void Variable_priority_queue::rescale(float factor)
{
    for (auto& [_, score] : pq)
    {
        score /= factor;
    }

    // Some scores may become equal in which case the heap invariant is broken (since we use
    // an ordering induced by `is_before()` which is not solely based on score).
    if (!pq.empty())
    {
        for (auto it = pq.begin() + (pq.size() - 1) / arity; it != pq.begin(); --it)
        {
            fix_down(it);
        }
        fix_down(pq.begin());
    }
}

void Variable_priority_queue::fix_up(Iterator it)
{
    for (; it != pq.begin(); it = parent(it))
    {
        auto parent_it = parent(it);
        if (is_before(*it, *parent_it))
        {
            swap(it, parent_it);
        }
    }
}

void Variable_priority_queue::fix_down(Iterator it)
{
    for (auto nodes = children(it); !nodes.empty(); nodes = children(it))
    {
        // find child with the maximum score
        auto max_it = nodes.begin();
        for (auto child_it = ++nodes.begin(); child_it != nodes.end(); ++child_it)
        {
            if (is_before(*child_it, *max_it))
            {
                max_it = child_it;
            }
        }

        // if the heap invariant is broken
        if (is_before(*max_it, *it))
        {
            swap(max_it, it);
            it = max_it;
        }
        else // the heap invariant is fixed
        {
            break;
        }
    }
}

} // namespace perun