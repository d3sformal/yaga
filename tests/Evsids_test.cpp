#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Database.h"
#include "Trail.h"
#include "Evsids.h"

TEST_CASE("Pick a variable with empty clause database", "[evsids]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 3);

    Evsids evsids;
    evsids.on_variable_resize(Variable::boolean, 3);
    evsids.on_init(db, trail);

    auto res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(0));
    model.set_value(0, true);
    trail.decide(res.value());

    res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(1));
    model.set_value(1, true);
    trail.decide(res.value());

    res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(2));
    model.set_value(2, true);
    trail.decide(res.value());

    REQUIRE(!evsids.pick(db, trail).has_value());
}

TEST_CASE("Pick the most used variable if there has not been a conflict", "[evsids]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    db.assert_clause(lit(0), lit(1), -lit(2));
    db.assert_clause(lit(0), -lit(1));
    db.assert_clause(lit(0));

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 3);

    Evsids evsids;
    evsids.on_variable_resize(Variable::boolean, 3);
    evsids.on_init(db, trail);

    auto res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(0));
    model.set_value(0, true);
    trail.decide(res.value());

    res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(1));
    model.set_value(1, true);
    trail.decide(res.value());

    res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(2));
    model.set_value(2, true);
    trail.decide(res.value());

    REQUIRE(!evsids.pick(db, trail).has_value());
}

TEST_CASE("Pick a variable after a large number of score decays", "[evsids]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    db.assert_clause(lit(0), lit(1), -lit(2));
    db.assert_clause(lit(0), -lit(1));
    db.assert_clause(lit(0));

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 3);

    Evsids evsids;
    evsids.on_variable_resize(Variable::boolean, 3);
    evsids.on_init(db, trail);

    auto learned = clause(lit(2));
    for (int i = 0; i < 10000; ++i)
    {
        evsids.on_learned_clause(db, trail, learned);
    }
    learned = clause(lit(1));
    for (int i = 0; i < 10; ++i)
    {
        evsids.on_learned_clause(db, trail, learned);
    }

    auto res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(2));
    model.set_value(2, true);
    trail.decide(res.value());

    res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(1));
    model.set_value(1, true);
    trail.decide(res.value());

    res = evsids.pick(db, trail);
    REQUIRE(res == bool_var(0));
    model.set_value(0, true);
    trail.decide(res.value());

    REQUIRE(!evsids.pick(db, trail).has_value());
}