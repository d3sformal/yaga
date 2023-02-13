#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Generalized_vsids.h"

TEST_CASE("Pick a variable with empty database", "[generalized_vsids]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;

    Trail trail;
    auto& bool_model = trail.set_model<bool>(Variable::boolean, 3);
    auto& real_model = trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 2);

    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::boolean, bool_model.num_vars());
    lra.on_variable_resize(Variable::rational, real_model.num_vars());

    Generalized_vsids vsids{lra};
    vsids.on_variable_resize(Variable::boolean, bool_model.num_vars());
    vsids.on_variable_resize(Variable::rational, real_model.num_vars());
    vsids.on_init(db, trail);

    auto res = vsids.pick(db, trail);
    REQUIRE(res.value() == Variable{0, Variable::boolean});

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(res.value() == Variable{1, Variable::boolean});

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(res.value() == Variable{2, Variable::boolean});

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(res.value() == Variable{0, Variable::rational});

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(res.value() == Variable{1, Variable::rational});

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(!res);
}

TEST_CASE("pick the most used variable at the start", "[generalized_vsids]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;

    Trail trail;
    auto& bool_model = trail.set_model<bool>(Variable::boolean, 0);
    auto& real_model = trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 2);

    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::boolean, bool_model.num_vars());
    lra.on_variable_resize(Variable::rational, real_model.num_vars());
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    db.assert_clause(clause(-linear(x < y), linear(y == 0)));
    db.assert_clause(clause(linear(x < y), linear(x == 0)));

    Generalized_vsids vsids{lra};
    vsids.on_variable_resize(Variable::boolean, bool_model.num_vars());
    vsids.on_variable_resize(Variable::rational, real_model.num_vars());
    vsids.on_init(db, trail);

    auto res = vsids.pick(db, trail);
    REQUIRE(res.value() == x);

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(res.value() == y);

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(res.value() == linear(x < y).lit().var());

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(res.value() == linear(y == 0).lit().var());

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(res.value() == linear(x == 0).lit().var());

    trail.propagate(res.value(), nullptr, 0);
    res = vsids.pick(db, trail);
    REQUIRE(!res);
}