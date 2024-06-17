#ifndef YAGA_YAGA_H
#define YAGA_YAGA_H

#include "Bool_theory.h"
#include "Clause.h"
#include "Evsids.h"
#include "Fraction.h"
#include "Generalized_vsids.h"
#include "Linear_constraint.h"
#include "Linear_arithmetic.h"
#include "Literal.h"
#include "Options.h"
#include "Rational.h"
#include "Restart.h"
#include "Solver.h"
#include "Term_manager.h"
#include "Term_types.h"
#include "Theory.h"
#include "Theory_combination.h"
#include "Uninterpreted_functions.h"
#include "Variable.h"
#include "Variable_order.h"

#include <algorithm>
#include <cassert>
#include <exception>
#include <ranges>

namespace yaga {

class Yaga;

class Initializer {
public:
    virtual ~Initializer() {}

    /** Initialize solver with the default configuration for a specific logic
     * 
     * @param solver solver to setup
     * @param options command line options
     */
    virtual void setup(Yaga* solver, Options const& options) const = 0;
};

class Propositional final : public Initializer {
public:
    virtual ~Propositional() = default;

    /** Initialize @p solver with only the plugin for boolean variables
     * 
     * @param solver solver to initializer
     * @param options command line options
     */
    void setup(Yaga* solver, Options const& options) const override;
};

/** Initializer for quantifier-free linear real arithmetic.
 */
class Qf_lra final : public Initializer {
public:
    virtual ~Qf_lra() = default;

    /** Initialize @p solver with plugins for boolean variables and rational variables.
     *
     * @param solver solver to initialize
     * @param options command line options
     */
    void setup(Yaga* solver, Options const& options) const override;
};

/** Initializer for quantifier-free linear real arithmetic with uninterpreted functions.
 */
class Qf_uflra final : public Initializer {
public:
    virtual ~Qf_uflra() = default;

    /** Initialize @p solver with plugins for boolean variables, rational variables and uninterpreted functions.
     * 
     * @param solver solver to initialize
     * @param options command line options
     */
    void setup(Yaga* solver, Options const& options) const override;
};

/** Predefined logic initializers for the Yaga facade.
 */
struct logic {
    /** Propositional logic
     */
    inline static Propositional const propositional{};

    /** Quantifier-free linear real arithmetic with uninterpreted functions
     */
    inline static Qf_uflra const qf_uflra{};

    /** Quantifier-free linear real arithmetic
     */
    inline static Qf_lra const qf_lra{};
};

/** A facade for the SMT solver.
 * 
 * Typical usage:
 * ~~~~~~~~~~~~~~~{.cpp}
 * Yaga smt{logic::qf_lra};
 * Variable x = smt.make(Variable::rational);
 * Variable y = smt.make(Variable::rational);
 * Literal a = smt.make_bool();
 * Literal b = smt.linear_constraint(std::array{x.ord(), y.ord()}, std::array<Rational, 2>{2, -1}, 
 *                                   Order_predicate::leq, 4);
 * smt.assert_clause(a);
 * smt.assert_clause(~a, b); 
 * auto result = smt.solver().check();
 * ~~~~~~~~~~~~~~~
 */
class Yaga {
public:

    /** Initialize the solver based on chosen logic.
     * 
     * @param init initializer for a logic
     * @param options solver options
     * @param tm term manager object from the parser
     */
    Yaga(terms::Term_manager const& tm,
         std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> > b_m,
         std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> > r_m);

    /** Reinitialize the solver with a different logic.
     * 
     * This operation removes all clauses and variables.
     * 
     * @param init initializer for a logic
     * @param options solver options
     */
    void init();

    void set_logic(Initializer const& init, Options const& options);

    bool has_uf();

    /** Create a new variable
     * 
     * @param type type of the new variable
     * @return object which represents the new variable
     */
    Variable make(Variable::Type type);

    /** Create a new variable representing a function application term
     *
     * @param type return type of the function
     * @return object which represents the function return value
     */
    Variable make_function_application(Variable::Type, terms::term_t);

    /** Convenience method to create new boolean variable and return a literal.
     * 
     * @return representation of the new boolean variable as a literal
     */
    Literal make_bool();

    /** Add a new linear constraint or return an old constraint if it already exists.
     * 
     * Constraints are normalized. Order of variables does not matter.
     * 
     * @tparam Var_range range of ordinal numbers (ints) of rational variables
     * @tparam Coef_range range of coefficients of variables (Rational)
     * @param vars variables in the constraint
     * @param coef coefficients of variables
     * @param pred constraint predicate (<, <=, =)
     * @param rhs constant term on the right-hand-side of the constraint
     * @return representation of the constraint as a literal
     */
    template<std::ranges::range Var_range, std::ranges::range Coef_range>
    Literal linear_constraint(Var_range&& vars, Coef_range&& coef, Order_predicate pred, Rational const& rhs)
    {
        if (!lra)
        {
            throw std::logic_error{"This logic does not support linear constraints."};
        }

        auto num_real_vars = static_cast<int>(solver().trail().model(Variable::rational).num_vars());
        for (auto&& var : vars)
        {
            if (var < 0 || var >= num_real_vars)
            {
                throw std::logic_error{"Rational variable " + std::to_string(var) + " is out of range."};
            }
        }

        return lra->constraint(smt.trail(), std::forward<Var_range>(vars), 
                               std::forward<Coef_range>(coef), pred, rhs).lit();
    }

    void propagate_mapping(std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> > mapping);
    void propagate_mapping(std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> > mapping);
    std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> > real_vars();
    std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> > bool_vars();

    std::optional<std::unordered_map<terms::term_t, Uninterpreted_functions::function_value_map_t>> get_function_model();

    /** Assert a new clause to the solver (range of literals)
     * 
     * @tparam Args types of arguments passed to Clause constructor
     * @param args arguments passed to Clause constructor
     */
    template <typename... Args> void assert_clause(Args&&... args) 
    { 
        smt.db().assert_clause(std::forward<Args>(args)...);
    }

    /** Get solver instance
     * 
     * @return yaga solver instance
     */
    inline Solver& solver() { return smt; }
private:
    Solver smt;

    // pointer to the LRA plugin or nullptr if this solver does not support LRA
    Linear_arithmetic* lra;

    // pointer to the UF plugin or nullptr if this solver does not support UF
    Uninterpreted_functions* uf;
    std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, int> > real_mapping;
    std::ranges::ref_view<const std::unordered_map<yaga::terms::term_t, Literal> > bool_mapping;
};

}

#endif // YAGA_YAGA_H