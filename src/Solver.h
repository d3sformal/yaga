#ifndef PERUN_SOLVER_H_
#define PERUN_SOLVER_H_

#include <array>
#include <memory>
#include <vector>
#include <algorithm>
#include <concepts>
#include <type_traits>

#include "Clause.h"
#include "Conflict_analysis.h"
#include "Database.h"
#include "Restart.h"
#include "Theory.h"
#include "Trail.h"
#include "Variable.h"
#include "Variable_order.h"
#include "Subsumption.h"
#include "Evsids.h"

namespace perun {

class Solver {
public:
    enum Result {
        unsat = 0,
        sat = 1
    };

    // get current trail (partial model)
    inline Trail& trail() { return trail_; }
    inline const Trail& trail() const { return trail_; }
    // get clause database associated with this solver
    inline Database& db() { return db_; }
    inline const Database& db() const { return db_; }

    // set theory used by the solver
    template<typename T, typename... Args>
        requires std::is_base_of_v<Theory, T>
    inline T& set_theory(Args&&... args)
    { 
        auto theory = std::make_unique<T>(std::forward<Args>(args)...);
        auto theory_ptr = theory.get();
        theory_ = std::move(theory);
        return *theory_ptr;
    }

    // set a new variable order heuristic
    template<typename T, typename... Args>
        requires std::is_base_of_v<Variable_order, T>
    inline void set_variable_order(Args&&... args)
    {
        variable_order_ = std::make_unique<T>(std::forward<Args>(args)...);
    }

    // set a new restart policy
    template<typename T, typename... Args>
        requires std::is_base_of_v<Restart, T>
    inline void set_restart_policy(Args&&... args)
    {
        restart_ = std::make_unique<T>(std::forward<Args>(args)...);
    }

    /** Check satisfiability of asserted clauses in database `db()`
     * 
     * @return `sat` if asserted clauses are satisfiable, `unsat` otherwise
     */
    Result check();

    // get total number of conflicts in the last check()
    inline int num_conflicts() const { return num_conflicts_; }
    // get total number of decisions in the last check()
    inline int num_decisions() const { return num_decisions_; }
    // get total number of restarts in the last check()
    inline int num_restarts() const { return num_restarts_; }
private:
    Trail trail_;
    Database db_;
    Subsumption subsumption_; 
    Conflict_analysis analysis_;
    std::unique_ptr<Theory> theory_;
    std::unique_ptr<Restart> restart_;
    std::unique_ptr<Variable_order> variable_order_;

    // statistics
    int num_conflicts_ = 0;
    int num_restarts_ = 0;
    int num_decisions_ = 0;

    // get all event listeners
    inline auto listeners()
    {
        return std::array<Event_listener*, 4>{
            theory_.get(),
            restart_.get(),
            variable_order_.get(),
            &subsumption_,
        };
    }

    std::optional<Clause> propagate();
    // analyze conflict clause
    std::pair<Clause, int> analyze_conflict(Clause&& conflict);
    // backtrack with conflict clause `learned` to assertion level `level`
    void backtrack_with(Clause&& learned, int level);
    // pick the next variable to assign
    std::optional<Variable> pick_variable();
    // decide value of an unassigned variable
    void decide(Variable var);
    // restart the solver
    void restart();
    // reset the solver for a new check()
    void init();
};

}

#endif // PERUN_SOLVER_H_