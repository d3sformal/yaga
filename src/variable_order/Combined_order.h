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
    template<class T, typename... Args>
        requires std::is_base_of_v<Variable_order, T>
    inline T& add(Args&&... args)
    {
        auto obj_ptr = std::make_unique<T>(std::forward<Args>(args)...);
        auto actual_ptr = obj_ptr.get();
        heuristics.emplace_back(std::move(obj_ptr));
        return *actual_ptr;
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

}

#endif // PERUN_COMBINED_ORDER_H