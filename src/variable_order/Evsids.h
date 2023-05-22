#ifndef YAGA_EVSIDS_H
#define YAGA_EVSIDS_H

#include <vector>

#include "Clause.h"
#include "Literal.h"
#include "Variable.h"
#include "Variable_order.h"

namespace yaga {

class Evsids final : public Variable_order {
public:
    virtual ~Evsids() = default;

    /** Reset VSIDS scores and initialize VSIDS scores by bumping all variables
     * in asserted clauses.
     *
     * @param db clause database
     * @param trail solver trail
     */
    void on_init(Database& db, Trail& trail) override;

    /** Allocate memory for VSIDS scores.
     *
     * @param type type of variable
     * @param num_vars new number of variables of type @p type
     */
    void on_variable_resize(Variable::Type type, int num_vars) override;

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

    /** Find an unassigned variable with the highest VSIDS score.
     *
     * @param db clause database
     * @param trail current solver trail
     * @return unassigned variable with the highest VSIDS score or none if all
     * variables are assigned
     */
    std::optional<Variable> pick(Database& db, Trail& trail) override;

    /** Check whether @p lhs has a greater VSIDS score than @p rhs
     * 
     * @param lhs first variable
     * @param rhs second variable
     * @return true iff @p lhs has a greater VSIDS score than @p rhs
     */
    bool is_before(Variable lhs, Variable rhs) const override;

    /** Get current VSIDS score of a boolean variable
     *
     * @param var_ord ordinal number of a boolean variable
     * @return VSIDS score of boolean variable @p var_ord
     */
    inline float score(int var_ord) const { return vsids[var_ord]; }

private:
    // map boolean variable ordinal -> VSIDS score
    std::vector<float> vsids;
    // score grow factor (inverse decay factor)
    float grow = 1.05f;
    // current amount by which a variable VSIDS is increased in `bump()`
    float inc = 1.0f;

    // when a score exceeds this threshold, all scores are rescaled
    inline static float const score_threshold = 1e35f;

    inline void rescale()
    {
        for (auto& score : vsids)
        {
            score /= score_threshold;
        }
        inc /= score_threshold;
    }

    inline void decay() { inc *= grow; }

    inline void bump(int var_ord)
    {
        vsids[var_ord] += inc;
        if (vsids[var_ord] >= score_threshold)
        {
            rescale();
        }
    }
};

} // namespace yaga

#endif // YAGA_EVSIDS_H