#ifndef PERUN_THEORY_COMBINATION_H
#define PERUN_THEORY_COMBINATION_H

#include <deque>
#include <memory>

#include "Theory.h"
#include "Variable.h"
#include "Database.h"
#include "Trail.h"
#include "Clause.h"

namespace perun {

/** Combination of several theories.
 */
class Theory_combination final : public Theory {
public:
    virtual ~Theory_combination() = default;

    /** Run propagate in all theories until no new propagations are generated.
     * 
     * @param db clause database
     * @param trail current solver trail
     * @return conflict clause if a conflict is detected by any theory
     */
    std::optional<Clause> propagate(Database&, Trail&) override;

    /** Call decide in all theories
     * 
     * @param db clause database
     * @param trail current solver trail
     * @param var variable to decide
     */
    void decide(Database&, Trail&, Variable) override;

    /** Call the event in all theories.
     * 
     * @param db clause database
     * @param trail current solver trail
     */
    void on_init(Database&, Trail&) override;

    /** Call the event in all theories.
     * 
     * @param type type of variables
     * @param num_vars new number of variables of type @p type
     */
    void on_variable_resize(Variable::Type, int) override;

    /** Call the event in all theories.
     * 
     * @param db clause database
     * @param trail current solver trail
     * @param learned newly learned clause
     */
    void on_learned_clause(Database&, Trail&, Clause const&) override;

    /** Call the event in all theories.
     * 
     * @param db clause database
     * @param trail current solver trail
     * @param other clause that is resolved with current conflict clause
     */
    void on_conflict_resolved(Database&, Trail&, Clause const&) override;

    /** Call the event in all theories.
     * 
     * @param db clause database
     * @param trail current solver trail
     */
    void on_restart(Database&, Trail&) override;

    /** Create a new theory and add it to this object.
     * 
     * @tparam T type of the theory to create
     * @tparam Args types of arguments passed to a constructor of T
     * @param args arguments forwarded to a constructor of T
     * @return reference to the new theory in this object
     */
    template<class T, typename... Args>
        requires std::is_base_of_v<Theory, T>
    inline T& add_theory(Args&&... args)
    {
        auto theory = std::make_unique<T>(std::forward<Args>(args)...);
        auto conc_theory_ptr = theory.get();
        theories.emplace_back(std::move(theory));
        return *conc_theory_ptr;
    }
private:
    std::deque<std::unique_ptr<Theory>> theories;
};

}

#endif // PERUN_THEORY_COMBINATION_H