#ifndef YAGA_UNINTERPRETED_FUNCTIONS_H
#define YAGA_UNINTERPRETED_FUNCTIONS_H

#include <algorithm>
#include <map>
#include <ranges>
#include <span>
#include <unordered_map>

#include "Linear_constraint.h"
#include "utils/Linear_polynomial.h"
#include "Term_manager.h"
#include "Term_types.h"
#include "Theory.h"
#include "Trail.h"

namespace yaga{

class Yaga;

class Uninterpreted_functions : public Theory {
public:
    using function_value_map_t = std::map<std::vector<terms::var_value_t>, terms::var_value_t>;

    Uninterpreted_functions(terms::Term_manager const& term_manager,
                            std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int>> rational_vars,
                            std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal>> bool_vars);

    /** Propagate literals to trail. In the case of conflicting function value assignments return a
     * conflict clause.
     *
     * @param db current solver clause database
     * @param trail current solver trail
     * @return conflict clause(s) resulting from new trail content
     */
    std::vector<Clause> propagate(Database& db, Trail& trail) override;

    /** Decide value for variable @p var. In the case of UF plugin, empty method (variable values
     * are managed by other plugins).
     */
    void decide(Database& db, Trail& trail, Variable var) override;

    /** Take action before the solver backtracks to decision level @p new_level
     *
     * @param db current solver clause database
     * @param trail current solver trail
     * @param new_level decision level the solver backtracks to
     */
    void on_before_backtrack(Database& db, Trail& trail, int new_level) override;

    /** Notify UF plugin of the existence of a function appication term
     *
     * @param var variable mapped to this application term
     * @param t application term
     */
    void register_application_term(Variable var, terms::term_t t);

    /** Provide the UF plugin with a pointer to the Yaga object which owns it
     *
     * @param yaga pointer to Yaga
     */
    void register_solver(Yaga* yaga);

    /** Get the current model of all uninterpreted funtions
     */
    std::unordered_map<terms::term_t, function_value_map_t> get_model();

private:
    struct Term_evaluation {
        terms::var_value_t value;
        int decision_level;
    };

    struct Function_application {
        terms::var_value_t value;
        terms::term_t app_term;
        int decision_level;
    };

    using function_application_map_t = std::map<std::vector<terms::var_value_t>, Function_application>;

    struct Variable_watch {
        Variable var;
        std::optional<int> decision_level;
    };

    class Assignment_watchlist {
    private:
        std::optional<Variable> watched_var;
        std::vector<Variable_watch> to_watch;
        terms::term_t term;
    public:
        Assignment_watchlist(terms::term_t, std::vector<Variable_watch>&&);
        std::optional<Variable> get_watched_var();
        terms::term_t get_term();
        // TODO - reimplement, no need for backtrack method
        void backtrack_to(int);
        void assign(Trail const&);
        bool all_assigned();
    };

    terms::Term_manager const& term_manager;
    std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int>> rational_vars;
    std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal>> bool_vars;
    std::vector<Assignment_watchlist> watchlists;
    std::unordered_map<terms::term_t, function_application_map_t> functions;
    std::unordered_map<terms::term_t, function_value_map_t> model;
    Yaga* solver;

    /** Evaluate term @p t with respect to current @p trail
     *
     * @param t term to evaluate
     * @param trail current solver trail
     * @return value of the term, and decision level of the term or maximum of its arguments
     */
    Term_evaluation evaluate(terms::term_t t, Trail& trail);

    /** Get list of non-constant arguments of @p t
     *
     * @param t term to analyze
     * @return vector of variables which must be assigned in order to evaluate @p t
     */
    std::vector<Variable> vars_to_watch(terms::term_t t);

    /** Check if there is a Variable directly mapped to @p t
     *
     * @param t term to check
     * @return Variable mapped to @p t or std::nullopt if there is none
     */
    std::optional<Variable> term_to_var(terms::term_t t);

    /** Store the value of the application term @p t and check for potential function application
     * conflicts
     *
     * @param t application term to evaluate
     * @param trail current solver trail
     * @return conflict clause(s) resulting from the new function value
     */
    std::vector<Clause> add_function_value(terms::term_t t, Trail& trail);

    /** Propagate the (dis)equality of terms @p t and @p u to the @p trail. Create a
     * linear constraint that forbids the current dis/equality of the terms and add it to the
     * conflict @p result_clause
     *
     * @param t term to compare
     * @param u term to compare
     * @param trail current solver trail
     * @param result_clause conflict clause for appending the new constraint
     * @param make_equal
     */
    void assert_equality(terms::term_t t, terms::term_t u, Trail& trail, Clause& result_clause, bool make_equal = true);

    /** Create a linear polynomial that represents term @p t
     *
     * @param t term to convert
     * @return linear polynomial representing @p t
     */
    utils::Linear_polynomial term_to_poly(terms::term_t t);
};

} // namespace yaga

#endif // YAGA_UNINTERPRETED_FUNCTIONS_H
