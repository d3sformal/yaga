#include "Uninterpreted_functions.h"
#include "Yaga.h"

namespace yaga {

void Uninterpreted_functions::Assignment_watchlist::backtrack_to(int new_lvl) {
    for (Variable_watch var_w : to_watch) {
        std::optional<int> maybe_lvl = var_w.decision_level;
        if (maybe_lvl.has_value() && maybe_lvl.value() > new_lvl) {
            var_w.decision_level = std::nullopt;

            if (! watched_var.has_value()) {
                watched_var = var_w.var;
            }
        }
    }
}

bool Uninterpreted_functions::Assignment_watchlist::all_assigned() {
    return ! watched_var.has_value();
}

Uninterpreted_functions::Assignment_watchlist::Assignment_watchlist(terms::term_t t, std::vector<Variable_watch>&& w_vector) : to_watch(w_vector), term(t)
{
    watched_var = w_vector[0].var;
}

std::optional<Variable> Uninterpreted_functions::Assignment_watchlist::get_watched_var()
{
    return watched_var;
}

terms::term_t Uninterpreted_functions::Assignment_watchlist::get_term()
{
    return term;
}

void Uninterpreted_functions::Assignment_watchlist::assign(Trail const& trail) {
    // To all variables, assign their current decision level
    for (Variable_watch& var_w : to_watch) {
        var_w.decision_level = trail.decision_level(var_w.var);
    }

    // Find a new watched variable, if there is one
    watched_var = std::nullopt;
    for (Variable_watch var_w : to_watch) {
        if (! var_w.decision_level.has_value()) {
            watched_var = var_w.var;
            break;
        }
    }
}

Uninterpreted_functions::Uninterpreted_functions(terms::Term_manager const& tm) : term_manager(tm) {}

std::vector<Clause> Uninterpreted_functions::propagate(Database&, Trail& trail) {
    printf("\n---Assignments---:\n");
    std::vector<Clause> result;

    for (Trail::Assignment const& assignment : trail.assigned(trail.decision_level())) {
        printf("#%i (%s)\n", assignment.var.ord(), assignment.var.type() == Variable::rational ? "rational" : "bool");
        for (Assignment_watchlist& w_list : watchlists) {
            if (! w_list.all_assigned() && assignment.var == w_list.get_watched_var().value()) {
                w_list.assign(trail);

                if (w_list.all_assigned()) {
                    std::vector<Clause> function_conflict = add_function_value(w_list.get_term(), trail);
                    result.insert(result.end(), function_conflict.begin(), function_conflict.end());
                }
            }
        }
    }

    /*
     * for each app term -> watchlist of unassigned arguments
     *   - create watchlist by examining structure of argument terms
     * after each `propagate` call, check all watchlists with all newly assigned variables
     * if the variable is watched, find a new unassigned argument
     * if there is none, all args are assigned -> find possible conflicting assignment in known function values (map from argument value tuples to function values)
     * for conflicting assignment, report conflict
     * for ok assignment, add it to the map
     *
     * =>
     * we need:
     * - when encountering an app term in internalizer, register it here (create watchlist)
     * - a function that evaluates a term
     *
     * DS:
     * - a vector of watchlists that have:
     *   - a list of pairs ( Variable, std::optional<int> ) - argument variables and their decision levels
     *   - their respective app term
     *
     * terms to Variables transformation (Internalizer):
     * - all terms substituted to one Variable, except:
     * - CONSTANT_TERM (terms::true_term), ARITH_CONSTANT, ARITH_PRODUCT, ARITH_POLY
     *
     */
    return result;
}

void Uninterpreted_functions::decide(yaga::Database&, yaga::Trail&, yaga::Variable) {
    // empty (decisions are made by other plugins)
}

void Uninterpreted_functions::register_mapping(std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> > mapping) {
    rational_vars = mapping;
}

void Uninterpreted_functions::register_mapping(std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> > mapping) {
    bool_vars = mapping;
}

std::optional<Variable> Uninterpreted_functions::term_to_var(terms::term_t t) {
    switch (term_manager.get_type(t)) {
    case terms::types::real_type: {
        auto key_equal = [=](std::pair<terms::term_t, int> p) { return p.first == t; };
        auto found = std::ranges::find_if(rational_vars, key_equal);
        if (found != rational_vars.end())
        {
            return Variable {found->second, Variable::rational};
        }
        break;
    }
    case terms::types::bool_type: {
        auto key_equal = [=](std::pair<terms::term_t, Literal> p) { return p.first == t; };
        auto found = std::ranges::find_if(bool_vars, key_equal);
        if (found != bool_vars.end())
        {
            return found->second.var();
        }
        break;
    }
    }

    return std::nullopt;
}

std::vector<Variable> Uninterpreted_functions::vars_to_watch(terms::term_t t) {
    std::vector<Variable> result;

    switch (term_manager.get_kind(t)) {
    case terms::Kind::ARITH_CONSTANT:
    case terms::Kind::CONSTANT_TERM:
        break;

    case terms::Kind::ARITH_PRODUCT:
    case terms::Kind::ARITH_POLY: {
        auto arg_terms = term_manager.get_args(t);
        for (auto arg_term : arg_terms) {
            auto vars = vars_to_watch(arg_term);
            result.insert(result.end(), vars.begin(), vars.end());
        }
        break;
    }

    default: {
        std::optional<Variable> maybe_var = term_to_var(t);
        if (maybe_var.has_value()) {
            result.push_back(maybe_var.value());
        }
    }
    }

    return result;
}

void Uninterpreted_functions::register_application_term(Variable var, terms::term_t app_term) {
    std::vector<Variable_watch> watch_vec;
    watch_vec.emplace_back(var, std::nullopt);
    for (auto arg_term : term_manager.get_args(app_term)) {
        std::vector<Variable> vars_to_watch = this->vars_to_watch(arg_term);
        for (Variable var_to_watch : vars_to_watch) {
            watch_vec.emplace_back(var_to_watch, std::nullopt);
        }
    }

    Assignment_watchlist w(app_term, std::move(watch_vec));
    watchlists.push_back(w);
}

void Uninterpreted_functions::register_solver(yaga::Yaga* s) {
    solver = s;
}

void Uninterpreted_functions::on_before_backtrack(Database&, Trail&, int new_lvl) {
    for (Assignment_watchlist& w : watchlists) {
        w.backtrack_to(new_lvl);
    }

}

Uninterpreted_functions::Term_evaluation Uninterpreted_functions::evaluate(const terms::term_t t, Trail& trail) {
    Term_evaluation result;

    std::optional<Variable> maybe_var = term_to_var(t);
    // If there is a Variable mapped directly to term t, return its value from the model
    if (maybe_var.has_value()) {
        assert(trail.decision_level(maybe_var.value()).has_value());

        switch (term_manager.get_type(t)) {
        case terms::types::real_type: {
            Model<Rational> model = trail.model<Rational>(Variable::rational);
            result.value = model.value(maybe_var.value().ord());
            break;
        }
        case terms::types::bool_type: {
            Model<bool> model = trail.model<bool>(Variable::boolean);
            result.value = model.value(maybe_var.value().ord());
            break;
        }
        }

        result.decision_level = trail.decision_level(maybe_var.value()).value();
        return result;
    }

    // Otherwise, compute the value from the arguments of term t
    switch (term_manager.get_kind(t)) {
    case terms::Kind::ARITH_CONSTANT:
        result.value = term_manager.arithmetic_constant_value(t);
        result.decision_level = 0;
        break;
    case terms::Kind::CONSTANT_TERM:
        result.value = true;
        result.decision_level = 0;
        break;
    case terms::Kind::ARITH_PRODUCT: {
        assert(term_manager.get_type(t) == terms::types::real_type);
        auto arg_terms = term_manager.get_args(t);
        Term_evaluation eval0 = evaluate(arg_terms[0], trail);
        Term_evaluation eval1 = evaluate(arg_terms[1], trail);
        Rational arg0 = std::get<Rational>(eval0.value);
        Rational arg1 = std::get<Rational>(eval1.value);
        result.value = arg0 * arg1;
        result.decision_level = std::max<int>(eval0.decision_level, eval1.decision_level);
        break;
    }
    case terms::Kind::ARITH_POLY: {
        assert(term_manager.get_type(t) == terms::types::real_type);
        auto arg_terms = term_manager.get_args(t);
        Rational sum = 0;
        int max_level = 0;
        for (auto arg_term : arg_terms)
        {
            Term_evaluation arg_eval = evaluate(arg_term, trail);
            terms::var_value_t arg_value = arg_eval.value;
            assert(std::holds_alternative<Rational>(arg_value));
            sum += std::get<Rational>(arg_value);
            max_level = std::max<int>(max_level, arg_eval.decision_level);
        }
        result.value = sum;
        result.decision_level = max_level;
        break;
    }
    default:
        throw std::logic_error("Unhandled evaluation case!");
    }

    return result;
}

// returns: a conflict clause
std::vector<Clause> Uninterpreted_functions::add_function_value(terms::term_t t, yaga::Trail& trail) {
    std::vector<terms::var_value_t> argument_values;
    int max_level = 0;
    for (terms::term_t arg_term : term_manager.get_args(t)) {
        Term_evaluation arg_eval = evaluate(arg_term, trail);
        argument_values.push_back(arg_eval.value);
        max_level = std::max<int>(max_level, arg_eval.decision_level);
    }

    Term_evaluation fnc_eval = evaluate(t, trail);
    terms::var_value_t function_value = fnc_eval.value;
    max_level = std::max<int>(max_level, fnc_eval.decision_level);

    terms::term_t fnc_symbol = term_manager.get_fnc_symbol(t);
    if (! functions.contains(fnc_symbol)) {
        functions[fnc_symbol] = function_application_map_t();
    }

    function_application_map_t& current_applications = functions.at(fnc_symbol);
    if (!current_applications.contains(argument_values)) {
        Function_application app;
        app.value = function_value;
        app.app_term = t;
        app.decision_level = max_level;

        current_applications[argument_values] = app;
        return {};
    }

    if (current_applications[argument_values].value == function_value) {
        return {};
    }

    // The new function value introduces a conflict

    // form a clause; literals:
    // - negation (Aarg1 == Barg1)
    // - negation (Aarg2 == Barg2)
    // - valA == valB

    return {};
}

std::unordered_map<terms::term_t, Uninterpreted_functions::function_value_map_t>& Uninterpreted_functions::get_model() {
    for (const auto& [term, function] : functions) {
        function_value_map_t function_values;
        for (const auto& [arg_values , fnc_app] : function) {
            function_values[arg_values] = fnc_app.value;
        }
        model[term] = function_values;
    }

    return model;
}

/*
 * TODO:
 *
 * we need -
 * - a function that takes two arguments (terms) and returns a Literal that represents their (in)equality
 * - to represent the decision level when storing a function value in the function value map
 *   (and when backtracking, remove this function value, if the decision level is too high)
 *
 */

} // namespace yaga