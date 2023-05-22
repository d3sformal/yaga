#ifndef YAGA_BOOL_THEORY_H
#define YAGA_BOOL_THEORY_H

#include <algorithm>
#include <optional>
#include <vector>
#include <ranges>

#include "Database.h"
#include "Literal.h"
#include "Literal_map.h"
#include "Model.h"
#include "Theory.h"
#include "Trail.h"

namespace yaga {

class Bool_theory : public Theory {
public:
    virtual ~Bool_theory() = default;

    /** Run BCP to exhaustion
     *
     * @param db clause database
     * @param trail current solver trail
     * @return conflict clause if there is a conflict, none otherwise.
     */
    std::vector<Clause> propagate(Database& db, Trail& trail) override;

    /** Decide value for variable @p var if it is a boolean variable
     *
     * @param db clause database
     * @param trail current solver trail
     * @param var variable to decide
     */
    void decide(Database& db, Trail& trail, Variable var) override;

    /** Initialize @p learned clause
     *
     * @param db clause database
     * @param trail current solver trail
     * @param learned reference to the learned clause in @p db
     */
    void on_learned_clause(Database& db, Trail& trail, Clause const& learned) override;

    /** Allocates memory for @p num_vars watch lists if @p type is boolean
     *
     * @param type variable type
     * @param num_vars new number of variables of type @p type
     */
    void on_variable_resize(Variable::Type, int) override;

private:
    // we move the watched literals to the first two position in each clause
    struct Watched_clause {
        // pointer to the watched clause in database
        Clause* clause;
        // the next index to check in clause
        int index;

        inline Watched_clause() {}
        inline explicit Watched_clause(Clause* clause)
            : clause(clause), index(std::min<int>(2, clause->size() - 1))
        {
        }
    };

    // satisfied literal with pointer to the reason clause (or nullptr)
    struct Satisfied_literal {
        // satisfied literal
        Literal lit;
        // clause that led to propagation of the literal or nullptr if there is none
        Clause* reason;

        /** Convert the structure to pair so we can tie the properties
         * 
         * @return pair of the values from this structure
         */
        inline operator std::pair<Literal, Clause*>() { return {lit, reason}; }
    };

    // map literal -> list of clauses in which it is watched
    Literal_map<std::vector<Watched_clause>> watched;
    // stack of true literals to propagate with a pointer to the reason clause
    std::vector<Satisfied_literal> satisfied;

    /** Propagate assigned literals at current decision level in @p trail
     *
     * @param db clause database
     * @param trail current trail
     */
    void initialize(Database& db, Trail& trail);

    /** Move watch from recently falsified literal @p lit to some other literal.
     *
     * -# If some clause becomes unit, this method will propagate the implied
     * literal by adding it to `satisfied`
     * -# If some clause becomes false, this method will return a copy of that
     * clause.
     *
     * @param trail current solver trail
     * @param model current assignment of boolean variables
     * @param lit recently falsified literal in @p model
     * @return conflict clause if a clause becomes false. None, otherwise.
     */
    std::optional<Clause> falsified(Trail const& trail, Model<bool> const& model, Literal lit);

    /** Try to replace the second watched literal in @p watch with some other
     * non-falsified literal
     *
     * @param model current assignment of boolean variables
     * @param watch
     * @return true iff the second watched literal has been replaced with some non-falsified 
     * literal in the clause
     */
    bool replace_second_watch(Model<bool> const& model, Watched_clause& watch);

    /** Make sure the second watched variable has the highest decision level in a unit or a false
     * clause.
     * 
     * Precondition: clause of @p watch is unit or false in @p model
     * 
     * @param trail current solver trail
     * @param model partial assignment of boolean variables
     * @param watch unit or false clause where the second watched variable is false
     * @return true iff the second watch has been replaced with a literal with higher decision 
     * level
     */
    bool fix_second_watch(Trail const& trail, Model<bool> const& model, Watched_clause& watch);
};

} // namespace yaga

#endif // YAGA_BOOL_THEORY_H