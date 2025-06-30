#include <unordered_map>

#include "test.h"
#include "Variable.h"
#include "Uninterpreted_functions.h"
#include "Yaga.h"

#include <catch2/catch_test_macros.hpp>

namespace yaga::test {

using r_map_t = std::unordered_map<yaga::terms::term_t, int>;
using b_map_t = std::unordered_map<yaga::terms::term_t, Literal>;

void propagate_var(Trail& trail, Literal lit)
{
    auto& model = trail.model<bool>(Variable::boolean);
    assert(!model.is_defined(lit.var().ord()));
    model.set_value(lit.var().ord(), !lit.is_negation());
    trail.propagate(lit.var(), nullptr, trail.decision_level());
}

void decide_lit(Trail& trail, Literal lit)
{
    auto& model = trail.model<bool>(Variable::boolean);
    assert(!model.is_defined(lit.var().ord()));
    model.set_value(lit.var().ord(), !lit.is_negation());
    trail.decide(lit.var());
}

// decide that a real variable var is equal to a value val
void decide_var(Trail& trail, Variable var, Rational value)
{
    auto& model = trail.model<Rational>(Variable::rational);
    assert(!model.is_defined(var.ord()));
    model.set_value(var.ord(), value);
    trail.decide(var);
}

Variable make_real_var_for_term(terms::term_t term, r_map_t& map, Yaga& yaga)
{
    Variable var = yaga.make(Variable::rational);
    map[term] = var.ord();
    return var;
}

Variable make_real_var_for_app_term(terms::term_t term, r_map_t& map, Yaga& yaga)
{
    Variable var = yaga.make_function_application(Variable::rational, term);
    map[term] = var.ord();
    return var;
}

TEST_CASE("UF: propagation introduces conflict", "[uf]")
{
    // f(x) == 0 && f(1) == 2 && x == 1

    using namespace yaga;
    using namespace yaga::test;

    terms::Term_manager tm;
    terms::term_t tx = tm.mk_uninterpreted_constant(terms::types::real_type);
    terms::term_t tf = tm.mk_uninterpreted_constant(terms::types::real_type);
    tm.set_term_name(tf, "f");
    terms::term_t t1 = tm.mk_rational_constant("1");

    std::array<terms::term_t, 1> txa = {tx};
    terms::term_t tfx = tm.mk_app("f", terms::types::real_type, txa);
    std::array<terms::term_t, 1> t1a = {t1};
    terms::term_t tf1 = tm.mk_app("f", terms::types::real_type, t1a);

    r_map_t rm;
    b_map_t bm;

    Yaga yaga(tm, std::ranges::views::all(rm), std::ranges::views::all(bm));
    yaga.set_logic(logic::qf_uflra, Options());

    Variable vx = make_real_var_for_term(tx, rm, yaga);
    Variable vfx = make_real_var_for_app_term(tfx, rm, yaga);
    Variable vf1 = make_real_var_for_app_term(tf1, rm, yaga);

    Trail& t = yaga.solver().trail();
    Database& db = yaga.solver().db();

    decide_var(t, vfx, 0);
    auto conflicts = yaga.solver().theory()->propagate(db, t);
    REQUIRE(conflicts.empty());

    decide_var(t, vf1, 2);
    conflicts = yaga.solver().theory()->propagate(db, t);
    REQUIRE(conflicts.empty());

    decide_var(t, vx, 1);
    conflicts = yaga.solver().theory()->propagate(db, t);
    REQUIRE(conflicts.size() == 1);
}

TEST_CASE("UF: valid function model", "[uf]")
{
    // f(x) == 0 && f(1) == 2 && x == 0

    using namespace yaga;
    using namespace yaga::test;

    terms::Term_manager tm;
    terms::term_t tx = tm.mk_uninterpreted_constant(terms::types::real_type);
    terms::term_t tf = tm.mk_uninterpreted_constant(terms::types::real_type);
    tm.set_term_name(tf, "f");
    terms::term_t t1 = tm.mk_rational_constant("1");

    std::array<terms::term_t, 1> txa = {tx};
    terms::term_t tfx = tm.mk_app("f", terms::types::real_type, txa);
    std::array<terms::term_t, 1> t1a = {t1};
    terms::term_t tf1 = tm.mk_app("f", terms::types::real_type, t1a);

    r_map_t rm;
    b_map_t bm;

    Yaga yaga(tm, std::ranges::views::all(rm), std::ranges::views::all(bm));
    yaga.set_logic(logic::qf_uflra, Options());
    yaga.solver().trail().resize(Variable::rational, 3); // TODO - is it necessary?

    Variable vx = make_real_var_for_term(tx, rm, yaga);
    Variable vfx = make_real_var_for_app_term(tfx, rm, yaga);
    Variable vf1 = make_real_var_for_app_term(tf1, rm, yaga);

    Trail& t = yaga.solver().trail();
    Database& db = yaga.solver().db();

    decide_var(t, vfx, 0);
    auto conflicts = yaga.solver().theory()->propagate(db, t);
    REQUIRE(conflicts.empty());

    decide_var(t, vf1, 2);
    conflicts = yaga.solver().theory()->propagate(db, t);
    REQUIRE(conflicts.empty());

    decide_var(t, vx, 0);
    conflicts = yaga.solver().theory()->propagate(db, t);
    REQUIRE(conflicts.empty());
}

TEST_CASE("UF: Parse a simple satisfiable formula", "[uf][sat][integration]")
{
    Yaga_test test;
    test.input() << "(set-logic QF_UFLRA)\n";
    test.input() << "(declare-fun x () Real)\n";
    test.input() << "(declare-fun y () Real)\n";
    test.input() << "(declare-fun f (Real) Real)\n";
    test.input() << "(assert (distinct (f x) (f y)))\n";
    test.run();

    REQUIRE(test.answer() == Solver_answer::SAT);
    REQUIRE(test.real("x").has_value());
    REQUIRE(test.real("y").has_value());
    auto x = *test.real("x");
    auto y = *test.real("y");
    REQUIRE(x != y);
    REQUIRE(test.fnc_value("f", {x}).has_value());
    REQUIRE(test.fnc_value("f", {y}).has_value());
    REQUIRE(*test.fnc_value("f", {x}) != *test.fnc_value("f", {y}));
}

TEST_CASE("UF: Parse a binary function", "[uf][sat][integration]")
{
    Yaga_test test;
    test.input() << "(set-logic QF_UFLRA)\n";
    test.input() << "(declare-fun x () Real)\n";
    test.input() << "(declare-fun y () Real)\n";
    test.input() << "(declare-fun f (Real Real) Real)\n";
    // implies x!=y && x!=0 && y!=0
    test.input() << "(assert (distinct (f 0 x) (f 0 y) (f x 0) (f y 0)))\n";
    test.run();

    REQUIRE(test.answer() == Solver_answer::SAT);
    REQUIRE(test.real("x").has_value());
    REQUIRE(test.real("y").has_value());
    auto x = *test.real("x");
    auto y = *test.real("y");
    REQUIRE(x != y);
    REQUIRE(x != 0);
    REQUIRE(y != 0);
    REQUIRE(test.fnc_value("f", {0, x}).has_value());
    REQUIRE(test.fnc_value("f", {0, y}).has_value());
    REQUIRE(test.fnc_value("f", {x, 0}).has_value());
    REQUIRE(test.fnc_value("f", {y, 0}).has_value());
    auto f_0_x = *test.fnc_value("f", {0, x});
    auto f_0_y = *test.fnc_value("f", {0, y});
    auto f_x_0 = *test.fnc_value("f", {x, 0});
    auto f_y_0 = *test.fnc_value("f", {y, 0});
    REQUIRE(f_0_x != f_0_y);
    REQUIRE(f_0_x != f_x_0);
    REQUIRE(f_0_x != f_y_0);
    REQUIRE(f_0_y != f_x_0);
    REQUIRE(f_0_y != f_y_0);
    REQUIRE(f_x_0 != f_y_0);
}

TEST_CASE("UF: Parse an unsat binary function", "[uf][unsat][integration]")
{
    Yaga_test test;
    test.input() << "(set-logic QF_UFLRA)\n";
    test.input() << "(declare-fun x () Real)\n";
    test.input() << "(declare-fun f (Real Real) Real)\n";
    test.input() << "(assert (distinct (f 0 x) (f x 0)))\n";
    test.input() << "(assert (= x 0))\n";
    test.run();

    REQUIRE(test.answer() == Solver_answer::UNSAT);
}

} // namespace yaga::test