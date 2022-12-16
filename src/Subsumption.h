#ifndef PERUN_SUBSUMPTION_H_
#define PERUN_SUBSUMPTION_H_

#include <vector>
#include <deque>
#include <cstdint>
#include <concepts>
#include <ranges>
#include <algorithm>
#include <unordered_set>

#include "Clause.h"
#include "Literal.h"
#include "Literal_map.h"
#include "Database.h"
#include "Trail.h"
#include "Variable.h"

namespace perun {

/** Periodically (on restart) removes subsumed clauses.
 * 
 * It also minimizes learned clauses using self-subsumption
 */
class Subsumption {
public:
    /** Event called whenever number of variables of type @p type changes
     * 
     * @param type type of variables
     * @param num_vars new number of variables
     */
    void on_variable_resize(Variable::Type type, int num_vars);

    /** Event called when a new conflict clause is learned but it has not been added to 
     * the database yet (i.e., before `on_learned_clause()`).
     * 
     * It minimizes @p conflict by removing literals that are 
     * 
     * @param db clause database
     * @param trail current trail
     * @param conflict clause in conflict with @p trail
     */
    void on_conflict_clause(Database& db, Trail& trail, Clause& conflict);

    /** Find and remove subsumed learned clauses
     * 
     * @param db clause database
     * @param trail current trail after restart
     */
    void on_restart(Database& db, Trail& trail);

private:
    // clause pointer proxy which also stores signature of the clause
    class Clause_ptr {
    public:
        inline Clause_ptr() {}
        inline Clause_ptr(const Clause* ptr, std::uint64_t sig) : ptr_(ptr), sig_(sig) {}
        inline const Clause* operator->() { return ptr_; }
        inline const Clause& operator*() { return *ptr_; }
        inline std::uint64_t sig() const { return sig_; }
        inline bool operator==(const Clause_ptr& other) const { return ptr_ == other.ptr_; }
        inline bool operator!=(const Clause_ptr& other) const { return !operator==(other); }
    private:
        // pointer to the clause
        const Clause* ptr_;
        // clause signature
        std::uint64_t sig_;
    };

    // compute signature of a clause and create a proxy object which includes this signature
    inline Clause_ptr make_proxy(const Clause* clause) const
    {
        Literal_hash hash;

        constexpr std::uint64_t MOD64 = (1 << 6) - 1; // bitmask for mod 64
        std::uint64_t sig = 0;
        for (auto lit : *clause)
        {
            sig |= 1UL << (hash(lit) & MOD64);
        }
        return {clause, sig};
    }

    // map literal -> clauses in which it occurs (created by index())
    Literal_map<std::vector<Clause_ptr>> occur_;
    // auxiliary bitset for subset tests in subsumes() and selfsubsumes()
    Literal_map<bool> bitset_;

    // check whether a literal is true in a model
    inline bool is_true(const Model<bool>& model, Literal lit) const 
    {
        return model.is_defined(lit.var().ord()) && 
               model.value(lit.var().ord()) == !lit.is_negation();
    }

    /** Construct `occur_` from learned clauses in @p db
     * 
     * @param db clause database
     */
    void index(const std::deque<Clause>& db);

    /** Check if @p first is a proper subset of @p second
     * 
     * @param first pointer to the first clause with its signature
     * @param second pointer to the second clause with its signature
     * @return true iff @p first is a proper subset of @p second
     */
    bool subsumes(Clause_ptr first, Clause_ptr second);

    /** Check if `resolve(first, second, lit)` is a proper subset of @p second
     * 
     * @param first first clause
     * @param second second clause
     * @param lit literal for resolution in @p first ; negation of a literal in @p second
     * @return true iff `resolve(first, second, lit)` is a proper subset of @p second
     */
    bool selfsubsumes(const Clause& first, const Clause& second, Literal lit);

    /** Remove clauses subsumed by @p clause from `occur_`
     * 
     * @param clause 
     * @param removed clauses subsumed by @p clause will be added to this set
     */
    void remove_subsumed(Clause_ptr clause, std::unordered_set<const Clause*>& removed);

    // removed subsumed clauses in the provided list
    void remove_subsumed(std::deque<Clause>& clauses);
};

}

#endif // PERUN_SUBSUMPTION_H_