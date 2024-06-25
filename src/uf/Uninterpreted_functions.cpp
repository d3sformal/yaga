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

Uninterpreted_functions::Uninterpreted_functions(terms::Term_manager const& tm,
                                                 std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> > r_m,
                                                 std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> > b_m)
    : term_manager(tm), rational_vars(r_m), bool_vars(b_m) {}

std::vector<Clause> Uninterpreted_functions::propagate(Database&, Trail& trail) {
    //printf("\n---Assignments---:\n");
    std::vector<Clause> result;

    std::vector<Trail::Assignment> assignments = trail.assigned(trail.decision_level());
    for (Trail::Assignment const& assignment : assignments) {
        //printf("#%i (%s)\n", assignment.var.ord(), assignment.var.type() == Variable::rational ? "rational" : "bool");
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
    for (auto & [_, function] : functions) {
        std::vector<std::vector<terms::var_value_t>> to_erase;
        for (auto & [arg_values, application] : function) {
            if (application.decision_level > new_lvl) {
                to_erase.push_back(arg_values);
            }
        }
        for (auto const& arg_values : to_erase) {
            function.erase(arg_values);
        }
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
            Model<Rational> const& r_model = trail.model<Rational>(Variable::rational);
            result.value = r_model.value(maybe_var.value().ord());
            break;
        }
        case terms::types::bool_type: {
            Model<bool> const& b_model = trail.model<bool>(Variable::boolean);
            bool bool_model_value = b_model.value(maybe_var.value().ord());
            result.value = bool_model_value;
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
        result.value = (t == terms::true_term);
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

utils::Linear_polynomial Uninterpreted_functions::term_to_poly(terms::term_t t) {
    assert(term_manager.get_type(t) == terms::types::real_type);

    std::optional<Variable> maybe_var = term_to_var(t);
    if (maybe_var.has_value()) {
        return {{maybe_var.value().ord()}, {1}, 0};
    }

    switch (term_manager.get_kind(t)) {
    case terms::Kind::ARITH_CONSTANT:
        return {{}, {}, term_manager.arithmetic_constant_value(t)};
    case terms::Kind::ARITH_PRODUCT: {
        Variable var = term_to_var(term_manager.var_of_product(t)).value();
        return {{var.ord()}, {term_manager.coeff_of_product(t)}, 0};
    }
    case terms::Kind::ARITH_POLY: {
        utils::Linear_polynomial p;
        auto const& args = term_manager.get_args(t);
        for (auto arg : args)
        {
            maybe_var = term_to_var(arg);
            if (maybe_var.has_value())
            {
                p.vars.push_back(maybe_var.value().ord());
                p.coef.emplace_back(1);
            }
            else if (term_manager.get_kind(arg) == terms::Kind::ARITH_CONSTANT)
            {
                p.constant = term_manager.arithmetic_constant_value(arg);
            }
            else
            {
                assert(term_manager.get_kind(arg) == terms::Kind::ARITH_PRODUCT);
                Variable var = term_to_var(term_manager.var_of_product(arg)).value();
                p.vars.push_back(var.ord());
                p.coef.push_back(term_manager.coeff_of_product(arg));
            }
        }
        return p;
    }
    default:
        throw std::logic_error("Unhandled 'term to polynomial' conversion case");
    }
}

void Uninterpreted_functions::assert_equality(terms::term_t t, terms::term_t u, Trail& trail, Clause& clause, bool make_equal = true) {
    assert(term_manager.get_type(t) == term_manager.get_type(u));
    switch(term_manager.get_type(t)) {
    case terms::types::real_type:
        // polynomial p == (t - u)
        utils::Linear_polynomial p = term_to_poly(t);
        p.sub(term_to_poly(u));

        if (p.vars.empty()) {
            assert(p.constant == 0);
            return;
        }

        Literal lit = solver->linear_constraint(p.vars, p.coef, Order_predicate::Type::eq, -p.constant);
        assert(!lit.is_negation());

        auto& trail_model = trail.model<bool>(Variable::boolean);

        if (!make_equal)
            lit.negate();

        bool propagate = true;

        // if the terms are not the same, we want them to be (and vice versa)
        bool are_equal = !make_equal;

        // no literal L can be propagated to the trail, if L or -L is already on the trail
        if (trail_model.is_defined(lit.var().ord())) {
            propagate = false;
        }

        if (propagate) {
            Term_evaluation t_eval = evaluate(t, trail);
            Term_evaluation u_eval = evaluate(u, trail);
            assert(are_equal == (t_eval.value == u_eval.value));

            int propagation_level = std::max<int>(t_eval.decision_level, u_eval.decision_level);
            trail.propagate(lit.var(), nullptr, propagation_level);
            trail_model.set_value(lit.var().ord(), are_equal);
        }

        clause.push_back(lit);
    }
}

// returns: a conflict clause (or more)
std::vector<Clause> Uninterpreted_functions::add_function_value(terms::term_t t, Trail& trail) {
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

    terms::term_t current_app_term = current_applications[argument_values].app_term;
    std::span<const terms::term_t> const& current_args = term_manager.get_args(current_app_term);
    std::span<const terms::term_t> const& conflict_args = term_manager.get_args(t);

    auto result = Clause();
    for (std::size_t i = 0; i < current_args.size(); ++i)
    {
        assert_equality(current_args[i], conflict_args[i], trail, result, false);
    }

    assert_equality(t, current_app_term, trail, result);

    return {result};
}

std::unordered_map<terms::term_t, Uninterpreted_functions::function_value_map_t> Uninterpreted_functions::get_model() {
    for (const auto& [term, function] : functions) {
        function_value_map_t function_values;
        for (const auto& [arg_values , fnc_app] : function) {
            function_values[arg_values] = fnc_app.value;
        }
        model[term] = function_values;
    }

    return model;
}

} // namespace yaga