#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Generalized_vsids.h"

TEST_CASE("Pick a variable with empty database", "[generalized_vsids]")
{
    using namespace yaga;
    using namespace yaga::test;

    Database db;
    Linear_arithmetic lra;
    Generalized_vsids vsids{lra};
    Event_dispatcher dispatcher;
    dispatcher.add(&lra);
    dispatcher.add(&vsids);
    Trail trail{dispatcher};
    trail.set_model<bool>(Variable::boolean, 3);
    trail.set_model<Rational>(Variable::rational, 2);

    dispatcher.on_init(db, trail);

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
    using namespace yaga;
    using namespace yaga::test;

    Database db;
    Linear_arithmetic lra;
    Generalized_vsids vsids{lra};
    Event_dispatcher dispatcher;
    dispatcher.add(&lra);
    dispatcher.add(&vsids);
    Trail trail{dispatcher};
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 2);

    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    db.assert_clause(clause(~linear(x < y), linear(y == 0)));
    db.assert_clause(clause(linear(x < y), linear(x == 0)));

    dispatcher.on_init(db, trail);

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