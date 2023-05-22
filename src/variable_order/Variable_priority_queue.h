#ifndef YAGA_VARIABLE_PRIORITY_QUEUE_H
#define YAGA_VARIABLE_PRIORITY_QUEUE_H

#include <algorithm>
#include <cassert>
#include <ranges>
#include <tuple>
#include <vector>

#include "Variable.h"

namespace yaga {

/** Implementation of a d-ary (max) heap which supports increasing variable scores.
 *
 * To disambiguate cases in which two scores are equal, we also use variable type and ordinal
 * to sort variables.
 */
class Variable_priority_queue {
public:
    using Score = float;

    /** Add a new variable to the priority queue
     *
     * Precondition: @p var is not in this priority queue
     *
     * @param var new variable to add to the queue
     * @param score initial score of @p var
     */
    void push(Variable var, Score score);

    /** Remove variable with the maximal score (`top()`) from the priority queue.
     *
     * Precondition: `!empty()`
     */
    void pop();

    /** Check whether @p var is in this priority queue
     *
     * @param var queried variable
     * @return true iff @p var is in this priority queue
     */
    inline bool contains(Variable var) const
    {
        return position.size() > var.type() &&
               position[var.type()].size() > static_cast<std::size_t>(var.ord()) &&
               position[var.type()][var.ord()] != missing;
    }

    /** Update score of @p var to @p score
     *
     * If @p var is not in the priority queue, this method does nothing.
     *
     * @param var variable to update
     * @param score new score of @p var
     */
    void update(Variable var, Score score);

    /** Divide all scores by @p factor
     *
     * @param factor constant by which all scores in the queue will be divided
     */
    void rescale(Score factor);

    /** Get variable with the highest score in this priority queue
     *
     * Precondition: `!empty()`
     *
     * @return variable with the highest score in this priority queue
     */
    inline Variable top()
    {
        assert(!empty());
        return pq.front().first;
    }

    /** Check whether this priority queue is empty
     *
     * @return true iff this priority queue is empty
     */
    inline bool empty() const { return pq.empty(); }

private:
    using Node = std::pair<Variable, Score>;
    using Iterator = std::vector<Node>::iterator;

    // priority queue
    std::vector<Node> pq;
    // position of a variable in the queue
    std::vector<std::vector<int>> position;

    // maximum number of children of a node
    inline static std::size_t constexpr arity = 4;
    // position of a variable which is not in the priority queue
    inline static int constexpr missing = -1;

    /** Check whether @p lhs is ordered before @p rhs
     *
     * @param lhs first variable
     * @param rhs second variable
     * @return true iff @p lhs is ordered before @p rhs
     */
    inline bool is_before(Variable lhs, Variable rhs) const
    {
        return lhs.type() < rhs.type() || (lhs.type() == rhs.type() && lhs.ord() < rhs.ord());
    }

    /** Check whether @p lhs is ordered before @p rhs
     *
     * @param lhs first node
     * @param rhs second node
     * @return true iff @p lhs is ordered before @p rhs
     */
    inline bool is_before(Node lhs, Node rhs) const
    {
        return lhs.second > rhs.second ||
               (lhs.second == rhs.second && is_before(lhs.first, rhs.first));
    }

    /** Find position of @p var in this priority queue
     *
     * @param var queried variable
     * @return position of @p var in this priority queue or end iterator if @p var is not in this
     * queue
     */
    inline Iterator find(Variable var)
    {
        if (position.size() <= var.type() ||
            position[var.type()].size() <= static_cast<std::size_t>(var.ord()) ||
            position[var.type()][var.ord()] < 0)
        {
            return pq.end();
        }
        return pq.begin() + position[var.type()][var.ord()];
    }

    /** Get iterator pointing at the parent of node at @p it
     *
     * @param it iterator pointing at a node
     * @return iterator pointing at the parent of node at @p it or @p it itself if @p it is the root
     */
    inline Iterator parent(Iterator it)
    {
        auto node_index = std::distance(pq.begin(), it);
        return node_index > 0 ? pq.begin() + (node_index - 1) / arity : pq.begin();
    }

    /** Get range of children of a node
     *
     * @param it iterator of a node
     * @return range of children of @p it
     */
    inline auto children(Iterator it)
    {
        auto node_index = std::distance(pq.begin(), it);
        auto begin_index = std::min<std::size_t>(node_index * arity + 1, pq.size());
        auto end_index = std::min<std::size_t>(begin_index + arity, pq.size());
        return std::ranges::subrange{pq.begin() + begin_index, pq.begin() + end_index};
    }

    /** Swap two nodes and variable positions
     *
     * @param first_node_it iterator pointing at the first node
     * @param second_node_it iterator pointing at the second node
     */
    inline void swap(Iterator first_node_it, Iterator second_node_it)
    {
        // swap nodes
        std::iter_swap(first_node_it, second_node_it);

        // update variable positions
        auto var = first_node_it->first;
        auto other_var = second_node_it->first;
        std::swap(position[var.type()][var.ord()], position[other_var.type()][other_var.ord()]);
    }

    /** Fix the heap invariant on the way up from @p it
     *
     * @param it iterator pointing at a node which (possibly) breaks the heap invariant on the way
     * to the root
     */
    void fix_up(Iterator it);

    /** Fix the heap invariant on the way from @p it to a leaf node
     *
     * @param it iterator pointing at a node which (possibly) breaks the heap invariant on a way
     * to a leaf
     */
    void fix_down(Iterator it);
};

} // namespace yaga

#endif // YAGA_VARIABLE_PRIORITY_QUEUE_H