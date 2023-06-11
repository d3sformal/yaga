#ifndef YAGA_YAGA_H
#define YAGA_YAGA_H

#include "Bool_theory.h"
#include "Clause.h"
#include "Fraction.h"
#include "Generalized_vsids.h"
#include "Linear_constraint.h"
#include "Linear_arithmetic.h"
#include "Literal.h"
#include "Solver.h"
#include "Variable.h"
#include "Theory.h"
#include "Theory_combination.h"
#include "Restart.h"
#include "Variable_order.h"
#include "Evsids.h"
#include "Rational.h"
#include "Options.h"

#include <algorithm>
#include <cassert>
#include <exception>
#include <ranges>

namespace yaga {

class Initializer {
public:
    virtual ~Initializer() {}

    /** Initialize solver with the default configuration for a specific logic
     * 
     * @param solver solver to setup
     * @param options command line options
     */
    virtual void setup(Solver& solver, Options const& options) const = 0;
};

class Propositional final : public Initializer {
public:
    virtual ~Propositional() = default;

    /** Initialize @p solver with only the plugin for boolean variables
     * 
     * @param solver solver to initializer
     * @param options command line options
     */
    void setup(Solver& solver, Options const& options) const override;
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
    void setup(Solver& solver, Options const& options) const override;
};

/** Predefined logic initializers for the Yaga facade.
 */
struct logic {
    /** Propositional logic
     */
    inline static Propositional const propositional{};

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
     */
    Yaga(Initializer const& init, Options const& options);

    /** Reinitialize the solver with a different logic.
     * 
     * This operation removes all clauses and variables.
     * 
     * @param init initializer for a logic
     * @param options solver options
     */
    void init(Initializer const& init, Options const& options);

    /** Create a new variable
     * 
     * @param type type of the new variable
     * @return object which represents the new variable
     */
    Variable make(Variable::Type type);

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
};

}

#endif // YAGA_YAGA_H