#ifndef PERUN_COMBINED_ORDER_H
#define PERUN_COMBINED_ORDER_H

#include <deque>
#include <memory>
#include <optional>
#include <type_traits>
#include <vector>

#include "Database.h"
#include "Trail.h"
#include "Variable_order.h"

namespace perun {

/** Uses a sequence of variable order heuristics.
 */
class Combined_order final : public Variable_order {
public:
    virtual ~Combined_order() = default;

    /** Create and add a new variable order heuristic to this object.
     *
     * @tparam T type of a variable order heuristic
     * @tparam Args types of arguments passed to a constructor of T
     * @param args arguments passed to a constructor of T
     * @return reference to the new heuristic in this object.
     */
    template <class T, typename... Args>
        requires std::is_base_of_v<Variable_order, T>
    inline T& add(Args&&... args)
    {
        auto obj_ptr = std::make_unique<T>(std::forward<Args>(args)...);
        auto actual_ptr = obj_ptr.get();
        heuristics.emplace_back(std::move(obj_ptr));
        return *actual_ptr;
    }

    /** Call the event on all managed heuristics
     *
     * @param db clause database
     * @param trail current solver trail
     */
    void on_init(Database& db, Trail& trail) override
    {
        for (auto& heuristic : heuristics)
        {
            heuristic->on_init(db, trail);
        }
    }

    /** Call the event on all managed heuristics
     *
     * @param type type of variables
     * @param num_vars new number of variables
     */
    void on_variable_resize(Variable::Type type, int num_vars) override
    {
        for (auto& heuristic : heuristics)
        {
            heuristic->on_variable_resize(type, num_vars);
        }
    }

    /** Call the event on all managed heuristics
     * 
     * @param db clause database
     * @param trail current solver trail before backtracking
     * @param level decision level to backtrack to
     */
    void on_before_backtrack(Database& db, Trail& trail, int level) override
    {
        for (auto& heuristic : heuristics)
        {
            heuristic->on_before_backtrack(db, trail, level);
        }
    }

    /** Call the event on all managed heuristics
     *
     * @param db clause database
     * @param trail current solver trail
     * @param learned reference to the newly learned clause in @p db
     */
    void on_learned_clause(Database& db, Trail& trail, Clause const& learned) override
    {
        for (auto& heuristic : heuristics)
        {
            heuristic->on_learned_clause(db, trail, learned);
        }
    }

    /** Call the event on all managed heuristics
     *
     * @param db clause database
     * @param trail current solver trail
     * @param other_clause clause that is resolved with current conflict clause
     */
    void on_conflict_resolved(Database& db, Trail& trail, Clause const& other) override
    {
        for (auto& heuristic : heuristics)
        {
            heuristic->on_learned_clause(db, trail, other);
        }
    }

    /** Call the event on all managed heuristics
     *
     * @param db clause database
     * @param trail current solver trail after restart
     */
    void on_restart(Database& db, Trail& trail) override
    {
        for (auto& heuristic : heuristics)
        {
            heuristic->on_restart(db, trail);
        }
    }

    /** Pick an unassigned variable using heuristics added by `add()`
     *
     * If no heuristic picks a variable, return none. Heuristics are used in order of their
     * addition.
     *
     * @param db clause database
     * @param trail current solver trail
     * @return unassigned variable return by a heuristic or none if all heuristics return none.
     */
    inline std::optional<Variable> pick(Database& db, Trail& trail) override
    {
        for (auto& heuristic : heuristics)
        {
            if (auto var = heuristic->pick(db, trail))
            {
                return var;
            }
        }
        return {};
    }

private:
    // variable order heuristics
    std::deque<std::unique_ptr<Variable_order>> heuristics;
};

} // namespace perun

#endif // PERUN_COMBINED_ORDER_H