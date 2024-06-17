#ifndef YAGA_SOLVER_H
#define YAGA_SOLVER_H

#include <algorithm>
#include <array>
#include <concepts>
#include <memory>
#include <type_traits>
#include <vector>
#include <ranges>

#include "Clause.h"
#include "Conflict_analysis.h"
#include "Database.h"
#include "Evsids.h"
#include "Event_listener.h"
#include "Event_dispatcher.h"
#include "Restart.h"
#include "Subsumption.h"
#include "Theory.h"
#include "Trail.h"
#include "Variable.h"
#include "Variable_order.h"

namespace yaga {

class Solver {
public:
    enum class Result { unsat = 0, sat = 1 };

    Solver();

    // non-copyable
    Solver(Solver const&) = delete;
    Solver& operator=(Solver const&) = delete;

    // movable
    Solver(Solver&&) = default;
    Solver& operator=(Solver&&) = delete;

    /** Get current trail (partial model)
     *
     * @return current trail
     */
    inline Trail& trail() { return solver_trail; }

    /** Get current trail (partial model)
     *
     * @return current trail
     */
    inline Trail const& trail() const { return solver_trail; }

    /** Get clause database used in `check()`
     *
     * @return clause database owned by this solver
     */
    inline Database& db() { return database; }

    /** Get clause database used in `check()`
     *
     * @return clause database owned by this solver
     */
    inline Database const& db() const { return database; }

    /** Create a new theory for this solver.
     *
     * @tparam T type of the theory
     * @tparam Args types of arguments of a constructor of T
     * @param args arguments passed to a constructor of T
     * @return reference to the theory in this solver
     */
    template <typename T, typename... Args>
        requires std::is_base_of_v<Theory, T>
    inline T& set_theory(Args&&... args)
    {
        dispatcher.remove(solver_theory.get());
        auto concrete_theory = std::make_unique<T>(std::forward<Args>(args)...);
        for (auto [type, model] : trail().models())
        {
            concrete_theory->on_variable_resize(type, model->num_vars());
        }

        auto concrete_theory_ptr = concrete_theory.get();
        solver_theory = std::move(concrete_theory);
        dispatcher.add(solver_theory.get());
        return *concrete_theory_ptr;
    }

    /** Create a new variable order heuristic for this solver.
     *
     * @tparam T type of the heuristic
     * @tparam Args types of arguments of a constructor of T
     * @param args arguments passed to a constructor of T
     * @return reference to the heuristic in this solver
     */
    template <typename T, typename... Args>
        requires std::is_base_of_v<Variable_order, T>
    inline T& set_variable_order(Args&&... args)
    {
        dispatcher.remove(variable_order.get());
        auto vo = std::make_unique<T>(std::forward<Args>(args)...);
        auto vo_ptr = vo.get();
        variable_order = std::move(vo);
        dispatcher.add(variable_order.get());
        return *vo_ptr;
    }

    /** Create a new restart policy for this solver.
     *
     * @tparam T type of the restart policy
     * @tparam Args types of arguments of a constructor of T
     * @param args arguments passed to a constructor of T
     * @return reference to the policy in this solver
     */
    template <typename T, typename... Args>
        requires std::is_base_of_v<Restart, T>
    inline T& set_restart_policy(Args&&... args)
    {
        dispatcher.remove(restart_policy.get());
        auto policy = std::make_unique<T>(std::forward<Args>(args)...);
        auto policy_ptr = policy.get();
        restart_policy = std::move(policy);
        dispatcher.add(restart_policy.get());
        return *policy_ptr;
    }

    /** Check satisfiability of asserted clauses in database `db()`
     *
     * @return `sat` if asserted clauses are satisfiable, `unsat` otherwise
     */
    Result check();

    /** Get total number of conflicts
     *
     * @return total number of conflicts in the last `check()`
     */
    inline int num_conflicts() const { return total_conflicts; }

    /** Get total number of decisions
     *
     * @return total number of decisions in the last `check()`
     */
    inline int num_decisions() const { return total_decisions; }

    /** Get number of restart
     *
     * @return total number of restarts in the last `check()`
     */
    inline int num_restarts() const { return total_restarts; }

    /** Get total number of generated conflict clauses
     * 
     * @return total number of conflict clauses in the last `check()`
     */
    inline int num_conflict_clauses() const { return total_conflict_clauses; }

    /** Get total number of learned clauses
     * 
     * @return total number of learned clauses in the last `check()`
     */
    inline int num_learned_clauses() const { return total_learned_clauses; }

    /** Get theory used by this solver
     * 
     * @return theory used by this solver or nullptr if no theory was set
     */
    inline Theory* theory() { return solver_theory.get(); }

private:
    Event_dispatcher dispatcher;
    Trail solver_trail;
    Database database;
    Conflict_analysis analysis;
    std::unique_ptr<Subsumption> subsumption;
    std::unique_ptr<Theory> solver_theory;
    std::unique_ptr<Restart> restart_policy;
    std::unique_ptr<Variable_order> variable_order;
    int num_bool_vars = 0;

    using Clause_iterator = std::deque<Clause>::iterator;
    using Clause_range = std::ranges::subrange<Clause_iterator>;

    // statistics
    int total_conflicts = 0;
    int total_conflict_clauses = 0;
    int total_learned_clauses = 0;
    int total_restarts = 0;
    int total_decisions = 0;

    // run propagate in theory
    [[nodiscard]] std::vector<Clause> propagate();
    // analyze conflict clauses
    [[nodiscard]] std::pair<std::vector<Clause>, int> analyze_conflicts(std::vector<Clause>&& conflict);
    // backtrack with conflict clauses to assertion level `level`
    void backtrack_with(Clause_range clauses, int level);
    // process all learned clauses and add them to database
    [[nodiscard]] Clause_range learn(std::vector<Clause>&& learned);
    // check if conflict `clause` is a semantic split clause
    bool is_semantic_split(Clause const& clause) const;
    // pick the next variable to assign
    [[nodiscard]] std::optional<Variable> pick_variable();
    // decide value of an unassigned variable
    void decide(Variable var);
    // restart the solver
    void restart();
    // reset the solver for a new check()
    void init();
};

} // namespace yaga

#endif // YAGA_SOLVER_H