#include "Solver_wrapper.h"
#include "Term_rewriter.h"
#include "Terms.h"

#include <algorithm>
#include <functional>
#include <unordered_set>
#include <variant>

namespace yaga::parser
{

using term_t = terms::term_t;

namespace {

std::vector<term_t> simplify_assertions(std::vector<term_t> assertions);

bool is_conjunction(terms::Term_manager const& tm, term_t term)
{
    return tm.is_negated(term) &&
           tm.get_kind(tm.positive_term(term)) == terms::Kind::OR_TERM;
}

void flatten_assertion(terms::Term_manager const& tm, term_t term, std::vector<term_t>& out)
{
    if (term == terms::true_term)
    {
        return;
    }
    if (term == terms::false_term)
    {
        out.push_back(term);
        return;
    }

    if (is_conjunction(tm, term))
    {
        for (term_t arg : tm.get_args(tm.positive_term(term)))
        {
            flatten_assertion(tm, terms::opposite_term(arg), out);
        }
        return;
    }

    out.push_back(term);
}

bool is_top_level_clause(terms::Term_manager const& tm, term_t term)
{
    return !tm.is_negated(term) &&
           tm.get_kind(term) == terms::Kind::OR_TERM;
}

void flatten_clause(terms::Term_manager const& tm, term_t term, std::vector<term_t>& out)
{
    if (is_top_level_clause(tm, term))
    {
        for (term_t arg : tm.get_args(term))
        {
            flatten_clause(tm, arg, out);
        }
        return;
    }

    out.push_back(term);
}

bool is_arithmetic_atom(terms::Term_manager const& tm, term_t term)
{
    switch (tm.get_kind(tm.positive_term(term)))
    {
    case terms::Kind::ARITH_GE_ATOM:
    case terms::Kind::ARITH_EQ_ATOM:
    case terms::Kind::ARITH_BINEQ_ATOM:
        return true;
    default:
        return false;
    }
}

bool is_linear_model_term(terms::Term_manager const& tm, term_t term)
{
    switch (tm.get_kind(term))
    {
    case terms::Kind::ARITH_CONSTANT:
    case terms::Kind::UNINTERPRETED_TERM:
        return true;
    case terms::Kind::ARITH_PRODUCT:
        return tm.is_uninterpreted(tm.var_of_product(term));
    case terms::Kind::ARITH_POLY:
        return std::ranges::all_of(tm.get_args(term), [&](term_t arg) {
            return is_linear_model_term(tm, arg);
        });
    default:
        return false;
    }
}

void add_linear_coeff(std::unordered_map<term_t, Rational>& coeffs, term_t term,
                      Rational const& coeff)
{
    if (coeff == 0)
    {
        return;
    }

    auto [it, inserted] = coeffs.insert({term, coeff});
    if (!inserted)
    {
        it->second += coeff;
        if (it->second == 0)
        {
            coeffs.erase(it);
        }
    }
}

bool collect_linear_terms(terms::Term_manager const& tm, term_t term,
                          std::unordered_map<term_t, Rational>& coeffs, Rational& constant)
{
    switch (tm.get_kind(term))
    {
    case terms::Kind::ARITH_CONSTANT:
        constant += tm.arithmetic_constant_value(term);
        return true;
    case terms::Kind::UNINTERPRETED_TERM:
        add_linear_coeff(coeffs, term, Rational{1});
        return true;
    case terms::Kind::ARITH_PRODUCT:
        if (!tm.is_uninterpreted(tm.var_of_product(term)))
        {
            return false;
        }
        add_linear_coeff(coeffs, tm.var_of_product(term), tm.coeff_of_product(term));
        return true;
    case terms::Kind::ARITH_POLY:
        for (term_t arg : tm.get_args(term))
        {
            if (!collect_linear_terms(tm, arg, coeffs, constant))
            {
                return false;
            }
        }
        return true;
    default:
        return false;
    }
}

bool contains_term(terms::Term_manager const& tm, term_t root, term_t needle)
{
    if (tm.positive_term(root) == needle)
    {
        return true;
    }
    for (term_t arg : tm.get_args(tm.positive_term(root)))
    {
        if (contains_term(tm, arg, needle))
        {
            return true;
        }
    }
    return false;
}

std::size_t term_size(terms::Term_manager const& tm, term_t root, std::size_t cap)
{
    std::size_t size = 1;
    if (size >= cap)
    {
        return cap;
    }

    for (term_t arg : tm.get_args(tm.positive_term(root)))
    {
        size += term_size(tm, arg, cap - size);
        if (size >= cap)
        {
            return cap;
        }
    }
    return size;
}

std::size_t count_occurrences(terms::Term_manager const& tm, std::span<term_t const> assertions,
                              std::size_t skip_idx, term_t needle, std::size_t cap)
{
    std::size_t count = 0;
    for (std::size_t i = 0; i < assertions.size() && count < cap; ++i)
    {
        if (i == skip_idx)
        {
            continue;
        }
        if (contains_term(tm, assertions[i], needle))
        {
            ++count;
        }
    }
    return count;
}

term_t rational_term(terms::Term_manager& tm, Rational const& value)
{
    return tm.mk_rational_constant(value.get_str());
}

term_t scaled_term(terms::Term_manager& tm, term_t term, Rational const& coeff)
{
    if (coeff == 1)
    {
        return term;
    }
    if (coeff == -1)
    {
        return tm.mk_unary_minus(term);
    }

    std::array<term_t, 2> args{rational_term(tm, coeff), term};
    return tm.mk_arithmetic_times(args);
}

term_t make_linear_term(terms::Term_manager& tm, std::unordered_map<term_t, Rational> const& coeffs,
                        Rational const& constant)
{
    std::vector<term_t> parts;
    parts.reserve(coeffs.size() + (constant == 0 ? 0 : 1));
    if (constant != 0)
    {
        parts.push_back(rational_term(tm, constant));
    }
    for (auto const& [term, coeff] : coeffs)
    {
        parts.push_back(scaled_term(tm, term, coeff));
    }

    if (parts.empty())
    {
        return terms::zero_term;
    }
    if (parts.size() == 1)
    {
        return parts.front();
    }
    return tm.mk_arithmetic_plus(parts);
}

std::optional<std::pair<term_t, term_t>> find_linear_definition(terms::Term_manager& tm,
                                                                std::span<term_t const> assertions,
                                                                std::size_t idx)
{
    constexpr std::size_t occurrence_limit = 8;
    constexpr std::size_t expr_size_limit = 48;

    auto assertion = assertions[idx];
    if (tm.is_negated(assertion))
    {
        return {};
    }

    auto positive = tm.positive_term(assertion);
    auto kind = tm.get_kind(positive);
    if (kind == terms::Kind::ARITH_BINEQ_ATOM)
    {
        auto args = tm.get_args(positive);
        std::optional<std::pair<term_t, term_t>> best;
        std::size_t best_occurrences = occurrence_limit + 1;

        for (int pivot_idx : {0, 1})
        {
            auto pivot = args[pivot_idx];
            auto expr = args[1 - pivot_idx];
            if (!tm.is_uninterpreted(pivot) || tm.get_type(pivot) != terms::types::real_type ||
                !is_linear_model_term(tm, expr) || contains_term(tm, expr, pivot))
            {
                continue;
            }

            auto occurrences =
                count_occurrences(tm, assertions, idx, pivot, occurrence_limit + 1);
            if (occurrences > occurrence_limit ||
                term_size(tm, expr, expr_size_limit + 1) > expr_size_limit)
            {
                continue;
            }
            if (!best || occurrences < best_occurrences)
            {
                best = {pivot, expr};
                best_occurrences = occurrences;
            }
        }
        return best;
    }

    if (kind != terms::Kind::ARITH_EQ_ATOM)
    {
        return {};
    }

    std::unordered_map<term_t, Rational> coeffs;
    Rational constant{0};
    if (!collect_linear_terms(tm, tm.get_args(positive)[0], coeffs, constant))
    {
        return {};
    }

    std::optional<std::pair<term_t, term_t>> best;
    std::size_t best_occurrences = occurrence_limit + 1;
    std::size_t best_size = expr_size_limit + 1;
    for (auto const& [pivot, pivot_coeff] : coeffs)
    {
        if (!tm.is_uninterpreted(pivot) || tm.get_type(pivot) != terms::types::real_type ||
            (pivot_coeff != 1 && pivot_coeff != -1))
        {
            continue;
        }

        std::unordered_map<term_t, Rational> rhs_coeffs;
        for (auto const& [term, coeff] : coeffs)
        {
            if (term == pivot)
            {
                continue;
            }
            add_linear_coeff(rhs_coeffs, term, -coeff / pivot_coeff);
        }
        auto rhs_constant = -constant / pivot_coeff;
        auto expr = make_linear_term(tm, rhs_coeffs, rhs_constant);
        if (contains_term(tm, expr, pivot))
        {
            continue;
        }

        auto occurrences = count_occurrences(tm, assertions, idx, pivot, occurrence_limit + 1);
        auto size = term_size(tm, expr, expr_size_limit + 1);
        if (occurrences > occurrence_limit || size > expr_size_limit)
        {
            continue;
        }
        if (!best || occurrences < best_occurrences ||
            (occurrences == best_occurrences && size < best_size))
        {
            best = {pivot, expr};
            best_occurrences = occurrences;
            best_size = size;
        }
    }
    return best;
}

std::vector<term_t> eliminate_linear_definitions(
    terms::Term_manager& tm, std::vector<term_t> assertions,
    std::unordered_map<term_t, term_t>& eliminated_terms)
{
    constexpr int substitution_budget = 512;

    for (int budget = substitution_budget; budget > 0; --budget)
    {
        bool changed = false;
        for (std::size_t i = 0; i < assertions.size(); ++i)
        {
            auto definition = find_linear_definition(tm, assertions, i);
            if (!definition)
            {
                continue;
            }

            auto [var, expr] = *definition;
            terms::subst_map_t substitution{{var, expr}};
            for (auto& [other_var, other_expr] : eliminated_terms)
            {
                if (other_var != var && contains_term(tm, other_expr, var))
                {
                    other_expr =
                        terms::simultaneous_variable_substitution(tm, substitution, other_expr);
                }
            }
            eliminated_terms[var] = expr;

            std::vector<term_t> rewritten;
            rewritten.reserve(assertions.size() - 1);
            for (std::size_t j = 0; j < assertions.size(); ++j)
            {
                if (j == i)
                {
                    continue;
                }

                auto current = assertions[j];
                rewritten.push_back(contains_term(tm, current, var)
                                        ? terms::simultaneous_variable_substitution(
                                              tm, substitution, current)
                                        : current);
            }

            assertions = simplify_assertions(std::move(rewritten));
            changed = true;
            break;
        }

        if (!changed)
        {
            break;
        }
    }

    return assertions;
}

std::optional<term_t> find_arithmetic_ite(terms::Term_manager const& tm, term_t root)
{
    std::vector<term_t> worklist;
    std::unordered_set<int32_t> seen;

    worklist.push_back(root);
    while (!worklist.empty())
    {
        auto current = worklist.back();
        worklist.pop_back();
        auto positive = tm.positive_term(current);
        if (!seen.insert(tm.index_of(positive)).second)
        {
            continue;
        }

        if (tm.get_kind(positive) == terms::Kind::ITE_TERM &&
            tm.get_type(positive) == terms::types::real_type)
        {
            return positive;
        }

        for (term_t arg : tm.get_args(positive))
        {
            worklist.push_back(arg);
        }
    }
    return {};
}

std::optional<std::pair<term_t, term_t>> constant_equality(terms::Term_manager const& tm, term_t term)
{
    if (tm.is_negated(term) || tm.get_kind(tm.positive_term(term)) != terms::Kind::ARITH_BINEQ_ATOM)
    {
        return {};
    }

    auto args = tm.get_args(tm.positive_term(term));
    if (tm.is_uninterpreted(args[0]) && tm.is_arithmetic_constant(args[1]))
    {
        return {{args[0], args[1]}};
    }
    if (tm.is_uninterpreted(args[1]) && tm.is_arithmetic_constant(args[0]))
    {
        return {{args[1], args[0]}};
    }
    return {};
}

std::optional<std::vector<std::pair<term_t, term_t>>>
uniform_constant_branch(terms::Term_manager const& tm, term_t branch)
{
    std::vector<term_t> conjuncts;
    flatten_assertion(tm, branch, conjuncts);

    std::vector<std::pair<term_t, term_t>> equalities;
    equalities.reserve(conjuncts.size());
    std::optional<term_t> branch_constant;
    for (term_t conjunct : conjuncts)
    {
        auto eq = constant_equality(tm, conjunct);
        if (!eq)
        {
            return {};
        }

        if (!branch_constant)
        {
            branch_constant = eq->second;
        }
        else if (*branch_constant != eq->second)
        {
            return {};
        }
        equalities.push_back(*eq);
    }

    return equalities;
}

std::optional<std::vector<term_t>> factor_uniform_choice(terms::Term_manager& tm, term_t assertion)
{
    if (tm.is_negated(assertion) || tm.get_kind(assertion) != terms::Kind::OR_TERM)
    {
        return {};
    }

    auto args = tm.get_args(assertion);
    if (args.size() != 2)
    {
        return {};
    }

    auto lhs = uniform_constant_branch(tm, args[0]);
    auto rhs = uniform_constant_branch(tm, args[1]);
    if (!lhs || !rhs || lhs->size() != rhs->size() || lhs->size() < 2)
    {
        return {};
    }

    std::unordered_map<term_t, term_t> rhs_values;
    rhs_values.reserve(rhs->size());
    for (auto const& [var, value] : *rhs)
    {
        rhs_values.insert({var, value});
    }

    std::vector<term_t> vars;
    vars.reserve(lhs->size());
    std::optional<term_t> lhs_value;
    std::optional<term_t> rhs_value;
    for (auto const& [var, value] : *lhs)
    {
        auto it = rhs_values.find(var);
        if (it == rhs_values.end())
        {
            return {};
        }
        if (!lhs_value)
        {
            lhs_value = value;
            rhs_value = it->second;
        }
        else if (*lhs_value != value || *rhs_value != it->second)
        {
            return {};
        }
        vars.push_back(var);
    }

    if (!lhs_value || !rhs_value || *lhs_value == *rhs_value)
    {
        return {};
    }

    std::vector<term_t> replacement;
    replacement.reserve(vars.size());
    auto const representative = vars.front();
    for (std::size_t i = 1; i < vars.size(); ++i)
    {
        replacement.push_back(tm.mk_binary_eq(representative, vars[i]));
    }
    replacement.push_back(
        tm.mk_binary_or(tm.mk_binary_eq(representative, *lhs_value),
                        tm.mk_binary_eq(representative, *rhs_value)));
    return replacement;
}

std::vector<term_t> simplify_assertions(std::vector<term_t> assertions)
{
    std::vector<term_t> result;
    result.reserve(assertions.size());
    std::unordered_set<term_t> seen;
    for (term_t assertion : assertions)
    {
        if (assertion == terms::true_term)
        {
            continue;
        }
        if (assertion == terms::false_term || seen.contains(terms::opposite_term(assertion)))
        {
            return {terms::false_term};
        }
        if (seen.insert(assertion).second)
        {
            result.push_back(assertion);
        }
    }
    return result;
}

std::vector<term_t> preprocess_assertions(terms::Term_manager& tm,
                                          std::vector<term_t> const& assertions,
                                          std::unordered_map<term_t, term_t>& eliminated_terms)
{
    std::vector<term_t> pending;
    pending.reserve(assertions.size());
    for (term_t assertion : assertions)
    {
        flatten_assertion(tm, assertion, pending);
    }
    pending = eliminate_linear_definitions(tm, std::move(pending), eliminated_terms);

    std::vector<term_t> result;
    result.reserve(pending.size());
    int ite_budget = 256;
    auto const expansion_cap = std::max<std::size_t>(1024, pending.size() * 16);

    while (!pending.empty())
    {
        auto assertion = pending.back();
        pending.pop_back();

        if (assertion == terms::true_term)
        {
            continue;
        }
        if (assertion == terms::false_term)
        {
            result.push_back(assertion);
            continue;
        }

        if (auto factored = factor_uniform_choice(tm, assertion))
        {
            pending.insert(pending.end(), factored->begin(), factored->end());
            continue;
        }

        if (ite_budget > 0 && pending.size() + result.size() < expansion_cap &&
            is_arithmetic_atom(tm, assertion))
        {
            if (auto ite = find_arithmetic_ite(tm, assertion))
            {
                auto args = tm.get_args(*ite);
                assert(args.size() == 3);

                terms::subst_map_t true_subst{{*ite, args[1]}};
                terms::subst_map_t false_subst{{*ite, args[2]}};

                auto on_true = terms::simultaneous_substitution(tm, true_subst, assertion);
                auto on_false = terms::simultaneous_substitution(tm, false_subst, assertion);

                pending.push_back(tm.mk_implies(args[0], on_true));
                pending.push_back(tm.mk_implies(terms::opposite_term(args[0]), on_false));
                --ite_budget;
                continue;
            }
        }

        result.push_back(assertion);
    }

    return simplify_assertions(std::move(result));
}

} // namespace

Solver_wrapper::Solver_wrapper(terms::Term_manager& term_manager, Options const& opts)
    : term_manager(term_manager), options(opts),
      internalizer_config(term_manager, solver), internalizer(term_manager, internalizer_config),
      solver(term_manager, internalizer_config.rational_vars(), internalizer_config.bool_vars()) {}

void Solver_wrapper::set_logic(Initializer const& init) {
    solver.set_logic(init, options);
}

bool Solver_wrapper::has_uf() {
    return solver.has_uf();
}

Solver_answer Solver_wrapper::check(std::vector<term_t> const& assertions)
{
    eliminated_rational_terms.clear();
    auto normalized_assertions =
        preprocess_assertions(term_manager, assertions, eliminated_rational_terms);
    if (std::ranges::any_of(normalized_assertions, [](term_t t) { return t == terms::false_term; }))
    {
        return Solver_answer::UNSAT;
    }

    // Cnfize and assert clauses to the solver
    solver.init();

    // Internalize all non-trivial terms first. For top-level disjunctions (CNF clauses), avoid
    // introducing an extra Tseitin variable and assert the clause directly.
    std::vector<term_t> to_internalize;
    to_internalize.reserve(normalized_assertions.size());
    for (term_t assertion : normalized_assertions)
    {
        if (assertion == terms::true_term)
        {
            continue;
        }

        if (is_top_level_clause(term_manager, assertion))
        {
            std::vector<term_t> clause_args;
            flatten_clause(term_manager, assertion, clause_args);
            for (term_t arg : clause_args)
            {
                to_internalize.push_back(arg);
            }
        }
        else
        {
            to_internalize.push_back(assertion);
        }
    }
    internalizer.visit(to_internalize);

    // add top level assertions to the solver
    for (term_t assertion : normalized_assertions)
    {
        if (assertion == terms::true_term) { continue; }

        if (is_top_level_clause(term_manager, assertion))
        {
            std::vector<term_t> args;
            flatten_clause(term_manager, assertion, args);
            std::vector<Literal> clause;
            clause.reserve(args.size());
            for (term_t arg : args)
            {
                auto pos_arg = term_manager.positive_term(arg);
                auto possibly_literal = internalizer_config.get_literal_for(pos_arg);
                assert(possibly_literal.has_value());
                Literal lit = possibly_literal.value();
                if (term_manager.is_negated(arg))
                {
                    lit.negate();
                }
                clause.push_back(lit);
            }

            std::sort(clause.begin(), clause.end(), Literal_comparer{});
            clause.erase(std::unique(clause.begin(), clause.end()), clause.end());

            bool tautology = false;
            for (std::size_t i = 0; i + 1 < clause.size(); ++i)
            {
                if (clause[i + 1] == ~clause[i])
                {
                    tautology = true;
                    break;
                }
            }

            if (!tautology)
            {
                solver.assert_clause(std::move(clause));
            }
        }
        else
        {
            auto possibly_literal = internalizer_config.get_literal_for(term_manager.positive_term(assertion));
            assert(possibly_literal.has_value());
            Literal literal = possibly_literal.value();
            if (term_manager.is_negated(assertion))
            {
                literal.negate();
            }
            solver.assert_clause(literal);
        }
    }

    // remember term-variable mapping
    variables.clear();

    for (auto& [term, lit] : internalizer_config.bool_vars())
    {
        if (term_manager.get_kind(term) == terms::Kind::UNINTERPRETED_TERM || term_manager.get_kind(term) == terms::Kind::APP_TERM)
        {
            variables.insert({term, lit.var()});
        }
    }
    for (auto& [term, var_ord] : internalizer_config.rational_vars())
    {
        if (term_manager.get_kind(term) == terms::Kind::UNINTERPRETED_TERM || term_manager.get_kind(term) == terms::Kind::APP_TERM)
        {
            variables.insert({term, Variable{var_ord, Variable::rational}});
        }
    }

    auto res = solver.solver().check();

    if (options.print_stats)
    {
        std::cout << "Conflicts = " << solver.solver().num_conflicts() << "\n";
        std::cout << "Conflict clauses = " << solver.solver().num_conflict_clauses() << "\n";
        std::cout << "Learned clauses = " << solver.solver().num_learned_clauses() << "\n";
        std::cout << "Decisions = " << solver.solver().num_decisions() << "\n";
        std::cout << "Restarts = " << solver.solver().num_restarts() << "\n";
    }

    if (res == Solver::Result::sat)
    {
        return Solver_answer::SAT;
    }
    else if (res == Solver::Result::unsat)
    {
        return Solver_answer::UNSAT;
    }
    assert(false);
    return Solver_answer::UNKNOWN;
}

void Solver_wrapper::model(Default_model_visitor& visitor)
{
    auto& bool_model = solver.solver().trail().model<bool>(Variable::boolean);
    auto& lra_model = solver.solver().trail().model<Rational>(Variable::rational);

    for (auto& [term, var] : variables)
    {
        if (term_manager.get_kind(term) != terms::Kind::UNINTERPRETED_TERM)
            continue;

        if (var.type() == Variable::boolean && bool_model.is_defined(var.ord()))
        {
            visitor.visit(term, static_cast<bool>(bool_model.value(var.ord())));
        }
        else if (var.type() == Variable::rational && lra_model.is_defined(var.ord()))
        {
            visitor.visit(term, lra_model.value(var.ord()));
        }
    }

    std::unordered_map<term_t, Rational> eliminated_cache;
    std::function<std::optional<Rational>(term_t)> eval_term = [&](term_t term)
        -> std::optional<Rational> {
        term = term_manager.positive_term(term);
        if (auto it = eliminated_cache.find(term); it != eliminated_cache.end())
        {
            return it->second;
        }

        std::optional<Rational> value;
        switch (term_manager.get_kind(term))
        {
        case terms::Kind::ARITH_CONSTANT:
            value = term_manager.arithmetic_constant_value(term);
            break;
        case terms::Kind::UNINTERPRETED_TERM:
            if (auto it = eliminated_rational_terms.find(term); it != eliminated_rational_terms.end())
            {
                value = eval_term(it->second);
            }
            else if (auto it = variables.find(term);
                     it != variables.end() && it->second.type() == Variable::rational &&
                     lra_model.is_defined(it->second.ord()))
            {
                value = lra_model.value(it->second.ord());
            }
            else
            {
                value = Rational{0};
            }
            break;
        case terms::Kind::ARITH_PRODUCT:
            if (auto inner = eval_term(term_manager.var_of_product(term)))
            {
                value = term_manager.coeff_of_product(term) * *inner;
            }
            break;
        case terms::Kind::ARITH_POLY:
        {
            Rational sum{0};
            for (term_t arg : term_manager.get_args(term))
            {
                auto arg_value = eval_term(arg);
                if (!arg_value)
                {
                    return {};
                }
                sum += *arg_value;
            }
            value = sum;
            break;
        }
        default:
            break;
        }

        if (value)
        {
            eliminated_cache.insert({term, *value});
        }
        return value;
    };

    for (auto const& [term, _] : eliminated_rational_terms)
    {
        if (variables.contains(term))
        {
            continue;
        }

        if (auto value = eval_term(term))
        {
            visitor.visit(term, *value);
        }
    }

    std::unordered_set<term_t> reported_free_terms;
    std::function<void(term_t)> report_free_terms = [&](term_t term) {
        term = term_manager.positive_term(term);
        if (term_manager.get_kind(term) == terms::Kind::UNINTERPRETED_TERM &&
            !variables.contains(term) && !eliminated_rational_terms.contains(term) &&
            reported_free_terms.insert(term).second)
        {
            visitor.visit(term, Rational{0});
        }

        for (term_t arg : term_manager.get_args(term))
        {
            report_free_terms(arg);
        }
    };

    for (auto const& [_, expr] : eliminated_rational_terms)
    {
        report_free_terms(expr);
    }

    auto fnc_model = solver.get_function_model();
    if (!fnc_model.has_value())
        return;

    for (auto const& fnc : fnc_model.value()) {
        auto fnc_term = fnc.first;
        auto fnc_values = fnc.second;
        visitor.visit_fnc(fnc_term, fnc_values);
    }
}

utils::Linear_polynomial Internalizer_config::internalize_poly(term_t t)
{
    auto kind = term_manager.get_kind(t);
    if (kind == terms::Kind::ARITH_CONSTANT)
    {
        return {{},{},term_manager.arithmetic_constant_value(t)};
    }
    if (kind == terms::Kind::UNINTERPRETED_TERM || kind == terms::Kind::ITE_TERM || kind == terms::Kind::APP_TERM)
    {
        return {{internal_rational_var(t)}, {1}, 0};
    }
    if (kind == terms::Kind::ARITH_PRODUCT)
    {
        return {{internal_rational_var(term_manager.var_of_product(t))},{term_manager.coeff_of_product(t)}, 0};
    }
    assert(kind == terms::Kind::ARITH_POLY);
    if (kind == terms::Kind::ARITH_POLY)
    {
        auto args = term_manager.get_args(t);
        utils::Linear_polynomial poly;
        poly.vars.reserve(args.size());
        poly.coef.reserve(args.size());
        assert(poly.constant == 0);
        for (term_t arg : args)
        {
            auto arg_kind = term_manager.get_kind(arg);
            if (arg_kind == terms::Kind::ARITH_CONSTANT)
            {
                poly.constant = term_manager.arithmetic_constant_value(arg);
            }
            else if (arg_kind == terms::Kind::UNINTERPRETED_TERM or arg_kind == terms::Kind::ITE_TERM or arg_kind == terms::Kind::APP_TERM)
            {
                poly.vars.push_back(internal_rational_var(arg));
                poly.coef.emplace_back(1);
            }
            else
            {
                assert(arg_kind == terms::Kind::ARITH_PRODUCT);
                poly.vars.push_back(internal_rational_var(term_manager.var_of_product(arg)));
                poly.coef.push_back(term_manager.coeff_of_product(arg));
            }
        }
        return poly;
    }
    throw std::logic_error("UNREACHABLE!");
}

void Internalizer_config::visit(term_t t)
{
    auto kind = term_manager.get_kind(t);
    switch (kind) {
    case terms::Kind::ARITH_GE_ATOM: {
        auto poly_term = term_manager.get_args(t)[0];
        assert(poly_term != terms::zero_term);
        auto internal_poly = internalize_poly(poly_term);
        bool negated = term_manager.is_negated(t);
        if (!negated) // We need to change "p >= 0" to "-p <= 0"
        {
            internal_poly.negate();
        }
        auto constraint_literal =
            negated ? solver.linear_constraint(internal_poly.vars, internal_poly.coef,
                                        Order_predicate::Type::lt, -internal_poly.constant)
                    : solver.linear_constraint(internal_poly.vars, internal_poly.coef,
                                        Order_predicate::Type::leq, -internal_poly.constant);
        Literal lit = negated ? ~constraint_literal : constraint_literal;
        term_t positive_term = term_manager.positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        internal_bool_vars.insert({positive_term, lit});
        return;
    }
    case terms::Kind::ARITH_EQ_ATOM: {
        auto poly_term = term_manager.get_args(t)[0];
        auto internal_poly = internalize_poly(poly_term);
        Literal lit = solver.linear_constraint(internal_poly.vars, internal_poly.coef, Order_predicate::Type::eq, -internal_poly.constant);
        assert(!lit.is_negation());
        term_t positive_term = term_manager.positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        internal_bool_vars.insert({positive_term, lit});
        return;
    }
    case terms::Kind::ARITH_BINEQ_ATOM: {
        auto args = term_manager.get_args(t);
        term_t lhs = args[0];
        term_t rhs = args[1];
        assert(term_manager.is_uninterpreted(lhs) || term_manager.is_ite(lhs));
        assert(term_manager.is_uninterpreted(rhs) || term_manager.is_ite(rhs) || term_manager.is_arithmetic_constant(rhs));
        auto poly = [&]() -> utils::Linear_polynomial {
            if (term_manager.is_arithmetic_constant(rhs))
            {
                return {{internal_rational_var(lhs)}, {1}, -term_manager.arithmetic_constant_value(rhs)};
            }
            else
            {
                return {{internal_rational_var(lhs), internal_rational_var(rhs)}, {1, -1}, 0};
            }
        }();
        Literal lit = solver.linear_constraint(poly.vars, poly.coef, Order_predicate::Type::eq, -poly.constant);
        assert(!lit.is_negation());
        term_t positive_term = term_manager.positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        internal_bool_vars.insert({positive_term, lit});
        return;
    }
    case terms::Kind::APP_TERM: {
        terms::type_t term_type = term_manager.get_type(t);
        Variable::Type var_type;
        switch (term_type) {
        case terms::types::real_type:
            var_type = Variable::rational;
            break;
        case terms::types::bool_type:
            var_type = Variable::boolean;
            break;
        }

        Variable var = solver.make_function_application(var_type, t);

        switch (term_type) {
        case terms::types::real_type:
            insert_var(internal_rational_vars, t, var.ord());
            break;
        case terms::types::bool_type:
            insert_var(internal_bool_vars, t, Literal(var.ord()));
            break;
        }

        return;
    }
    case terms::Kind::UNINTERPRETED_TERM:
        if (term_manager.get_type(t) == terms::types::bool_type)
        {
            Variable bool_var = solver.make(Variable::boolean);
            t = term_manager.positive_term(t);
            insert_var(internal_bool_vars, t, Literal(bool_var.ord()));
        }
        else if (term_manager.get_type(t) == terms::types::real_type)
        {
            Variable rational_var = solver.make(Variable::rational);
            insert_var(internal_rational_vars, t, rational_var.ord());
        }
        return;
    case terms::Kind::OR_TERM:
    {
        auto args = term_manager.get_args(t);
        assert(args.size() >= 2);
        assert(std::all_of(args.begin(), args.end(), [&](term_t t){return term_manager.get_type(t) == terms::types::bool_type;}));
        term_t positive_term = term_manager.positive_term(t);
        assert(internal_bool_vars.find(positive_term) == internal_bool_vars.end());
        Variable var = new_bool_var();
        Literal lit = Literal(var.ord());
        internal_bool_vars.insert({positive_term, lit});
        std::vector<Literal> arg_literals;
        arg_literals.reserve(args.size());
        for (term_t arg : args)
        {
            term_t pos_arg = term_manager.positive_term(arg);
            assert(internal_bool_vars.find(pos_arg) != internal_bool_vars.end());
            auto arg_lit = internal_bool_vars.at(pos_arg);
            if (term_manager.is_negated(arg))
            {
                arg_lit.negate();
            }
            arg_literals.push_back(arg_lit);
        }
        // binary clauses
        for (auto arg_lit : arg_literals)
        {
            solver.assert_clause(lit, ~arg_lit);
        }
        // big clause
        arg_literals.push_back(~lit);
        solver.assert_clause(std::move(arg_literals));
        return;
    }
    case terms::Kind::ITE_TERM:
    {
        // Extend if we decide to enable boolean ITEs as well
        assert(term_manager.get_type(t) == terms::types::real_type);
        if (term_manager.get_type(t) == terms::types::real_type)
        {
            auto args = term_manager.get_args(t);
            term_t cond_term = args[0];
            term_t true_branch = args[1];
            term_t false_branch = args[2];
            auto var = new_real_var();
            assert(internal_rational_vars.find(t) == internal_rational_vars.end());
            internal_rational_vars.insert({t, var.ord()});
            auto true_poly = internalize_poly(true_branch);
            auto false_poly = internalize_poly(false_branch);
            // Let v = ite(c, t, f). Then we assert that c => (t = v) and ~c => (f = v)
            true_poly.subtract_var(var);
            false_poly.subtract_var(var);
            // TODO: Must the variables be sorted?
            auto true_constraint = solver.linear_constraint(true_poly.vars, true_poly.coef, Order_predicate::Type::eq, -true_poly.constant);;
            auto false_constraint = solver.linear_constraint(false_poly.vars, false_poly.coef, Order_predicate::Type::eq, -false_poly.constant);
            assert(!term_manager.is_negated(cond_term)); // MB: ITE are normalized to have positive condition
            assert(internal_bool_vars.find(cond_term) != internal_bool_vars.end());
            Literal l = internal_bool_vars.at(cond_term);
            solver.assert_clause(l, false_constraint);
            solver.assert_clause(~l, true_constraint);
        }
        return;
    }

    case terms::Kind::CONSTANT_TERM:
    {
        if (t != terms::true_term)
        {
            throw std::logic_error("Unhandled internalize case!");
        }
        return;
    }

    case terms::Kind::ARITH_CONSTANT:
    case terms::Kind::ARITH_PRODUCT:
    case terms::Kind::ARITH_POLY:
        return;
    default:
        throw std::logic_error("Unhandled internalize case!");
    }
}

std::optional<Literal> Internalizer_config::get_literal_for(term_t t) const
{
    auto it = internal_bool_vars.find(t);
    return it == internal_bool_vars.end() ? std::optional<Literal>{} : it->second;
}

} // namespace yaga::parser
