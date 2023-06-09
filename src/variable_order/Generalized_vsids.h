#ifndef YAGA_GENERALIZED_VSIDS_H
#define YAGA_GENERALIZED_VSIDS_H

#include <array>
#include <map>
#include <optional>
#include <queue>
#include <vector>

#include "Linear_arithmetic.h"
#include "Variable_order.h"
#include "Variable_priority_queue.h"

namespace yaga {

/** This class computes scores similar to VSIDS from SAT solvers (`Evsids`). When a score of
 * a boolean function is bumped, all variables which implement the function are also bumped.
 *
 * Limitation: at the moment, only boolean variables and rational variables managed by
 * the LRA plugin are supported.
 */
class Generalized_vsids final : public Variable_order {
public:
    using Score = float;

    virtual ~Generalized_vsids() = default;

    inline Generalized_vsids(Linear_arithmetic& lra) : lra(&lra) {}

    /** Allocate memory for variable VSIDS scores
     *
     * @param type type of a variable
     * @param num_vars new number of variables of type @p type
     */
    void on_variable_resize(Variable::Type type, int num_vars) override;

    /** Reset VSIDS of all variables to 0 and bump all asserted/learned variables.
     *
     * @param db clause database
     * @param trail current solver trail
     */
    void on_init(Database& db, Trail& trail) override;

    /** Add all unassigned variables back to an internal priority queue
     *
     * @param db clause database
     * @param trail solver trail before backtracking
     * @param level new decision level to backtrack to
     */
    void on_before_backtrack(Database& db, Trail& trail, int level) override;

    /** Bump variables in @p learned and decay VSIDS scores.
     *
     * @param db clause database
     * @param trail current solver trail
     * @param learned reference to the newly learned clause in @p db
     */
    void on_learned_clause(Database& db, Trail& trail, Clause const& learned) override;

    /** Bump variables in @p other
     *
     * @param db clause database
     * @param trail current solver trail
     * @param other clause that has just been resolved with conflict clause in
     * conflict analysis
     */
    void on_conflict_resolved(Database& db, Trail& trail, Clause const& other) override;

    /** Pick a variable with the best VSIDS score.
     *
     * @param db clause database
     * @param trail current solver trail
     * @return unassigned variable with the best VSIDS score or none, if all variables are assigned
     */
    std::optional<Variable> pick(Database& db, Trail& trail) override;

    /** Check whether @p lhs has a greater VSIDS score than @p rhs
     * 
     * @param lhs first variable
     * @param rhs second variable
     * @return true iff @p lhs has a greater VSIDS score than @p rhs
     */
    bool is_before(Variable lhs, Variable rhs) const override;

    /** Get current VSIDS score of @p var
     * 
     * @param var queried variable
     * @return VSIDS score of @p var
     */
    inline Score score(Variable var) const 
    { 
        if (vsids.size() <= var.type() || vsids[var.type()].size() <= static_cast<std::size_t>(var.ord()))
        {
            return 0.f;
        }
        return vsids[var.type()][var.ord()]; 
    }
private:
    // map variable type -> variable ordinal -> VSIDS score
    std::vector<std::vector<Score>> vsids;
    // priority queue of variables sorted by VSIDS score
    Variable_priority_queue variables;
    // priority queue of effectively decided variables sorted by the VSIDS score
    Variable_priority_queue effectively_decided;
    // score grow factor (inverse decay factor)
    Score grow = 1.05;
    // current amount by which a variable VSIDS is increased in `bump()`
    Score inc = 1.0;
    // LRA plugin with linear constraints
    Linear_arithmetic* lra;

    // when a score exceeds this threshold, all scores are rescaled
    inline static Score const score_threshold = 1e35;

    /** Pick the variable with the highest VSIDS score
     * 
     * @param trail the current solver trail
     * @return the unassigned variable with the highest VSIDS score or none if all variables are 
     * assigned
     */
    std::optional<Variable> pick_top(Trail& trail);

    /** Try to pick a rational variable with only one allowed value.
     * 
     * @param trail the current solver trail
     * @return effectively decided variable or none if no variable is effectively decided
     */
    std::optional<Variable> pick_effectively_decided(Trail& trail);

    // get VSIDS score of a variable
    inline Score& score(Variable var) { return vsids[var.type()][var.ord()]; }

    // divide all scores by `score_threshold`
    inline void rescale()
    {
        for (auto& scores : vsids)
        {
            for (auto& score : scores)
            {
                score /= score_threshold;
            }
        }
        inc /= score_threshold;
        variables.rescale(score_threshold);
        effectively_decided.rescale(score_threshold);
    }

    // decay all VSIDS scores (by increasing the amount by which VSIDS scores are increased)
    inline void decay() { inc *= grow; }

    inline void bump(int bool_var_ord)
    {
        bump(Variable{bool_var_ord, Variable::boolean});
        for (auto lra_var_ord : lra->constraint(bool_var_ord).vars())
        {
            bump(Variable{lra_var_ord, Variable::rational});
        }
    }

    // bump VSIDS score of `var`
    inline void bump(Variable var)
    {
        score(var) += inc;
        if (score(var) >= score_threshold)
        {
            rescale();
        }
        else
        {
            variables.update(var, score(var));
            effectively_decided.update(var, score(var));
        }
    }
};

} // namespace yaga

#endif // YAGA_GENERALIZED_VSIDS_H