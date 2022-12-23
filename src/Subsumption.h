#ifndef PERUN_SUBSUMPTION_H
#define PERUN_SUBSUMPTION_H

#include <algorithm>
#include <concepts>
#include <cstdint>
#include <deque>
#include <ranges>
#include <vector>

#include "Clause.h"
#include "Database.h"
#include "Event_listener.h"
#include "Literal.h"
#include "Literal_map.h"
#include "Model.h"
#include "Trail.h"
#include "Variable.h"

namespace perun {

/** Periodically (on restart) removes subsumed clauses.
 *
 * It also minimizes learned clauses using self-subsumption
 */
class Subsumption final : public Event_listener {
public:
    void on_variable_resize(Variable::Type type, int num_vars) override;
    // minimize conflict using self-subsuming resolution
    void on_conflict_derived(Database& db, Trail& trail, Clause& conflict) override;
    // find and remove subsumed learned clauses from db
    void on_restart(Database& db, Trail& trail) override;

private:
    // Clause pointer proxy which also stores signature of the clause.
    // Signature is a 64-bit mask of the clause such that if a clause A is a
    // subset of a clause B, then A.sig() is a subset of B.sig() (but not
    // necessarily vice versa)
    class Clause_ptr {
    public:
        inline Clause_ptr() {}
        inline Clause_ptr(Clause* ptr, std::uint64_t sig) : ptr_(ptr), sig_(sig) {}
        inline Clause_ptr(Clause_ptr const&) = default;
        inline Clause_ptr& operator=(Clause_ptr const&) = default;
        inline Clause* operator->() { return ptr_; }
        inline Clause& operator*() { return *ptr_; }
        inline std::uint64_t sig() const { return sig_; }
        inline bool operator==(Clause_ptr const& other) const { return ptr_ == other.ptr_; }
        inline bool operator!=(Clause_ptr const& other) const { return !operator==(other); }

    private:
        // pointer to the clause
        Clause* ptr_;
        // clause signature
        std::uint64_t sig_;
    };
    // map literal -> clauses in which it occurs (created by index())
    Literal_map<std::vector<Clause_ptr>> occur_;
    // auxiliary bitset for subset tests in subsumes() and selfsubsumes()
    Literal_map<bool> bitset_;

    // compute signature of a clause and create a proxy object which includes
    // this signature
    inline Clause_ptr make_proxy(Clause* clause) const
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

    /** Construct `occur_` from learned clauses in @p db
     *
     * @param db clause database
     */
    void index(std::deque<Clause>& db);

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
     * @param lit literal for resolution in @p first ; negation of a literal in
     * @p second
     * @return true iff `resolve(first, second, lit)` is a proper subset of @p
     * second
     */
    bool selfsubsumes(Clause const& first, Clause const& second, Literal lit);

    /** Mark clauses subsumed by @p clause (by making them empty)
     *
     * @param clause
     */
    void remove_subsumed(Clause_ptr clause);

    // removed subsumed learned clauses
    void remove_subsumed(Database& db);
};

} // namespace perun

#endif // PERUN_SUBSUMPTION_H