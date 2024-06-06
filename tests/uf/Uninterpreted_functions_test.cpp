#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Uninterpreted_functions.h"

#include <ranges>

TEST_CASE("UF: propagation introduces conflict", "[uninterpreted_functions]")
{
    // test:
    // f(0) == 0
    // f(x) == 1
    // x == 0
    // => conflict

    using namespace yaga;
    using namespace yaga::test;

    terms::Term_manager tm;
    terms::term_t fnc_term = tm.mk_uninterpreted_constant(terms::types::real_type);
    tm.set_term_name(fnc_term, "f");

    auto zero = std::vector<terms::term_t>{tm.mk_integer_constant("0")};
    auto x = tm.mk_uninterpreted_constant(terms::types::real_type);
    auto x_v = std::vector<terms::term_t>{x};

    terms::term_t app0 = tm.mk_app("f", terms::types::real_type, zero);
    terms::term_t app1 = tm.mk_app("f", terms::types::real_type, x_v);
    auto var0 = Variable(0, Variable::rational);
    auto var1 = Variable(1, Variable::rational);
    auto varx = Variable(2, Variable::rational);

    std::unordered_map<terms::term_t, int> term_to_var;
    term_to_var[app0] = 0;
    term_to_var[app1] = 1;
    term_to_var[x] = 2;

    const std::unordered_map<terms::term_t, int> const_map = term_to_var;

    Uninterpreted_functions uf(tm);
    Yaga yaga(logic::qf_uflra, Options(), tm);
    uf.register_solver(&yaga);
    uf.register_mapping(const_map);
    uf.register_application_term(var0, app0);
    uf.register_application_term(var1, app1);

    auto& trail = yaga.solver().trail();
    trail.resize(Variable::rational, 3);
    auto& model = trail.model<Rational>(Variable::rational);

    trail.decide(var0);
    model.set_value(0, 0);
    auto conflicts = uf.propagate(yaga.solver().db(), yaga.solver().trail());
    REQUIRE(conflicts.empty());
    // f(0) has an evaluation representative and is assigned to 0
    REQUIRE(std::get<Rational> (uf.get_model().at(fnc_term).at({0})) == (Rational) 0);

    trail.decide(var1);
    model.set_value(1, 1);
    conflicts = uf.propagate(yaga.solver().db(), yaga.solver().trail());
    REQUIRE(conflicts.empty());
    // f(x) does not have an evaluation representative yet
    REQUIRE(uf.get_model().at(fnc_term).size() == 1);

    trail.decide(varx);
    model.set_value(2, 0);
    conflicts = uf.propagate(yaga.solver().db(), yaga.solver().trail());
    REQUIRE(!conflicts.empty());



}