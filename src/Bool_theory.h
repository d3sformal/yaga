#ifndef PERUN_BOOL_THEORY_H_
#define PERUN_BOOL_THEORY_H_

#include <optional>
#include <vector>
#include <algorithm>

#include "Database.h"
#include "Model.h"
#include "Theory.h"
#include "Trail.h"
#include "Literal.h"
#include "Literal_map.h"

namespace perun {

class Bool_theory : public Theory {
public:
    virtual ~Bool_theory() = default;

    // run BCP to exhaustion
    std::optional<Clause> propagate(Database& db, Trail& trail) override;

    // decide value for variable var if it is a boolean variable
    void decide(Database& db, Trail& trail, Variable var) override;

    // initialize the learned clause
    void on_learned_clause(Database& db, Trail& trail, Clause* learned) override;

private:
    // we move the watched literals to the first two position in each clause
    struct Watched_clause {
        // pointer to the watched clause in database
        Clause* clause;
        // the next index to check in clause
        int index;

        inline Watched_clause() {}
        inline explicit Watched_clause(Clause* clause) : clause(clause), index(std::min<int>(2, clause->size())) {}
    };

    // map literal -> list of clauses in which it is watched
    Literal_map<std::vector<Watched_clause>> watched_;
    // stack of true literals to propagate with a pointer to the reason clause
    std::vector<std::pair<Literal, Clause*>> propagate_;

    /** Initialize propagate for all assigned literals at current level in @p trail
     * 
     * @param db clause database
     * @param trail current trail
     * @return conflict clause if a clause becomes false. Otherwise, nothing.
     */
    std::optional<Clause> initialize(Database& db, Trail& trail);

    /** Move watch from recently falsified literal @p lit to some other literal. 
     * 
     * -# If some clause becomes unit, this method will propagate the implied literal by adding it to `propagate_`
     * -# If some clause becomes false, this method will return a copy of that clause.
     * 
     * @param model current assignment of boolean variables 
     * @param lit recently falsified literal in @p model
     * @return conflict clause if a clause becomes flase. Otherwise, nothing.
     */
    std::optional<Clause> falsified(const Model<bool>& model, Literal lit);

    /** Try to replace the second watched literal in @p watch with some other non-falsified literal
     * 
     * @param model current assignment of boolean variables
     * @param watch 
     * @return true iff the second watched literal has been replaced with some other non-falsified
     * literal in the clause
     */
    bool replace_second_watch(const Model<bool>& model, Watched_clause& watch);
};

}

#endif // PERUN_BOOL_THEORY_H_