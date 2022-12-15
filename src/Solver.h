#ifndef PERUN_SOLVER_H_
#define PERUN_SOLVER_H_

#include <memory>
#include <vector>
#include <algorithm>
#include <concepts>
#include <type_traits>

#include "Clause.h"
#include "Conflict_analysis.h"
#include "Database.h"
#include "Theory.h"
#include "Trail.h"
#include "Variable.h"
#include "Variable_order.h"

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

    // add a new theory to the solver
    template<typename T, typename... Args>
        requires std::is_base_of_v<Theory, T>
    inline T& add_theory(Args&&... args)
    { 
        auto theory = std::make_unique<T>(std::forward<Args>(args)...);
        auto theory_ptr = theory.get();
        theories_.emplace_back(std::move(theory));
        return *theory_ptr;
    }

    // set a new variable order heuristic
    template<typename T, typename... Args>
        requires std::is_base_of_v<Variable_order, T>
    inline void set_variable_order(Args&&... args)
    {
        variable_order_ = std::make_unique<T>(std::forward<Args>(args)...);
    }

    /** Check satisfiability of asserted clauses in database `db()`
     * 
     * @return `sat` if asserted clauses are satisfiable, `unsat` otherwise
     */
    Result check();

private:
    Trail trail_;
    Database db_;
    Conflict_analysis analysis_;
    std::unique_ptr<Variable_order> variable_order_;
    std::vector<std::unique_ptr<Theory>> theories_;

    std::optional<Clause> propagate();
    // analyze conflict clause
    std::pair<Clause, int> analyze_conflict(Clause&& conflict);
    // backtrack with conflict clause `learned` to assertion level `level`
    void backtrack_with(Clause&& learned, int level);
    // pick the next variable to assign
    std::optional<Variable> pick_variable();
    // decide value of an unassigned variable
    void decide(Variable var);
};

}

#endif // PERUN_SOLVER_H_