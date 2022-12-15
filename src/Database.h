#ifndef PERUN_DATABASE_H_
#define PERUN_DATABASE_H_

#include <deque>
#include <vector>

#include "Literal.h"
#include "Clause.h"

namespace perun {

class Database {
public:
    /** Add a new clause that is part of the input formula.
     * 
     * @tparam Args argument types for Clause constructor
     * @param args arguments for Clause constructor
     */
    template<typename... Args>
    inline void assert_clause(Args&&... args)
    {
        asserted_.emplace_back(Clause{std::forward<Args>(args)...});
    }

    /** Add a clause that is implied by asserted clauses to the database.
     * 
     * @tparam Args argument types for Clause constructor
     * @param args arguments for Clause constructor
     * @return reference to the clause in this database
     */
    template<typename... Args>
    inline Clause& learn_clause(Args&&... args)
    {
        return learned_.emplace_back(Clause{std::forward<Args>(args)...});
    }

    // get learned clauses
    inline auto& learned() { return learned_; }
    inline const auto& learned() const { return learned_; }
    // get range of asserted clauses
    inline auto& asserted() { return asserted_; }
    inline const auto& asserted() const { return asserted_; }

private:
    std::deque<Clause> learned_;
    std::deque<Clause> asserted_;
};

}

#endif // PERUN_DATABASE_H_