#ifndef PERUN_DATABASE_H
#define PERUN_DATABASE_H

#include <deque>
#include <vector>

#include "Clause.h"
#include "Literal.h"

namespace perun {

class Database {
public:
    /** Add a new clause that is part of the input formula.
     *
     * @tparam Args argument types for Clause constructor
     * @param args arguments for Clause constructor
     */
    template <typename... Args> inline Clause& assert_clause(Args&&... args)
    {
        return asserted_clauses.emplace_back(Clause{std::forward<Args>(args)...});
    }

    /** Add a clause that is implied by asserted clauses to the database.
     *
     * @tparam Args argument types for Clause constructor
     * @param args arguments for Clause constructor
     * @return reference to the clause in this database
     */
    template <typename... Args> inline Clause& learn_clause(Args&&... args)
    {
        return learned_clauses.emplace_back(Clause{std::forward<Args>(args)...});
    }

    /** Get all learned clauses
     *
     * @return reference to a range with learned clauses.
     */
    inline auto& learned() { return learned_clauses; }

    /** Get all learned clauses
     *
     * @return reference to a range with learned clauses.
     */
    inline auto const& learned() const { return learned_clauses; }

    /** Get all asserted clauses
     *
     * @return reference to a range with asserted clauses
     */
    inline auto& asserted() { return asserted_clauses; }

    /** Get all asserted clauses
     *
     * @return reference to a range with asserted clauses
     */
    inline auto const& asserted() const { return asserted_clauses; }

private:
    std::deque<Clause> learned_clauses;
    std::deque<Clause> asserted_clauses;
};

} // namespace perun

#endif // PERUN_DATABASE_H