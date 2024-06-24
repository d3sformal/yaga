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

    Uninterpreted_functions(terms::Term_manager const&,
                            std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> >,
                            std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> >);
    std::vector<Clause> propagate(Database&, Trail&) override;
    void decide(Database&, Trail&, Variable) override;
    void on_before_backtrack(Database&, Trail&, int) override;
    void register_application_term(Variable, terms::term_t);
    void register_mapping(std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> > );
    void register_mapping(std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> > );
    void register_solver(Yaga*);
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

    Term_evaluation evaluate(terms::term_t, Trail&);
    std::vector<Variable> vars_to_watch(terms::term_t);
    std::optional<Variable> term_to_var(terms::term_t);
    std::vector<Clause> add_function_value(terms::term_t, Trail&);
    void assert_equality(terms::term_t, terms::term_t, Trail&, Clause&, bool);
    utils::Linear_polynomial term_to_poly(terms::term_t);
};

} // namespace yaga

#endif // YAGA_UNINTERPRETED_FUNCTIONS_H
