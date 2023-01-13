#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_floating_point.hpp>

#include "test.h"
#include "Restart.h"
#include "Trail.h"

TEST_CASE("Restart when average of recent LBDs exceeds average of LBDs", "[glucose]")
{
    using namespace perun;
    using namespace perun::test;

    Glucose_restart restart;
    restart.set_min_conflicts(0);
    restart.set_slow_exp(3);
    restart.set_fast_exp(2);

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 9);
    trail.decide(bool_var(0));
    trail.propagate(bool_var(1), nullptr, 1);
    trail.decide(bool_var(2));
    trail.propagate(bool_var(3), nullptr, 2);
    trail.propagate(bool_var(4), nullptr, 2);
    trail.decide(bool_var(5));
    trail.decide(bool_var(6));
    trail.propagate(bool_var(7), nullptr, 4);
    trail.propagate(bool_var(8), nullptr, 4);

    REQUIRE(restart.should_restart());

    auto learned = clause(lit(1), lit(6), lit(7)); // LBD = 2
    restart.on_learned_clause(db, trail, learned);
    REQUIRE_THAT(restart.slow(), Catch::Matchers::WithinRel(2.f / 8));
    REQUIRE_THAT(restart.fast(), Catch::Matchers::WithinRel(2.f / 4));
    REQUIRE(restart.should_restart());

    learned = clause(lit(8)); // LBD = 1
    restart.on_learned_clause(db, trail, learned);
    REQUIRE_THAT(restart.slow(), Catch::Matchers::WithinRel(2.f / 8 + (1.f - 2.f / 8) / 8));
    REQUIRE_THAT(restart.fast(), Catch::Matchers::WithinRel(2.f / 4 + (1.f - 2.f / 4) / 4));
    REQUIRE(restart.should_restart());

    learned = clause(lit(2), lit(3), lit(4)); // LBD = 1
    restart.on_learned_clause(db, trail, learned);
    REQUIRE_THAT(restart.slow(), Catch::Matchers::WithinRel(0.34375f + (1 - 0.34375f) / 8));
    REQUIRE_THAT(restart.fast(), Catch::Matchers::WithinRel(0.625f + (1 - 0.625f) / 4));
    REQUIRE(restart.should_restart());

    for (int i = 0; i < 5; ++i)
    {
        learned = clause(lit(2)); // LBD = 1
        restart.on_learned_clause(db, trail, learned);
        REQUIRE(restart.should_restart());
    }

    learned = clause(lit(2)); // LBD = 1
    restart.on_learned_clause(db, trail, learned);
    REQUIRE(!restart.should_restart());
}

TEST_CASE("Wait for a minimum number of conflicts before restart", "[glucose]")
{
    using namespace perun;
    using namespace perun::test;

    Glucose_restart restart;
    restart.set_min_conflicts(2);
    restart.set_slow_exp(3);
    restart.set_fast_exp(2);

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 9);
    trail.decide(bool_var(0));
    trail.propagate(bool_var(1), nullptr, 1);
    trail.decide(bool_var(2));
    trail.propagate(bool_var(3), nullptr, 2);
    trail.propagate(bool_var(4), nullptr, 2);
    trail.decide(bool_var(5));
    trail.decide(bool_var(6));
    trail.propagate(bool_var(7), nullptr, 4);
    trail.propagate(bool_var(8), nullptr, 4);

    REQUIRE(!restart.should_restart());

    auto learned = clause(lit(0)); 
    restart.on_learned_clause(db, trail, learned);
    REQUIRE(!restart.should_restart());

    learned = clause(lit(0)); 
    restart.on_learned_clause(db, trail, learned);
    REQUIRE(restart.should_restart());
}

TEST_CASE("Compute clause LBD if decision levels of literals are not consecutive", "[glucose]")
{
    using namespace perun;
    using namespace perun::test;

    Glucose_restart restart;
    restart.set_min_conflicts(0);
    restart.set_slow_exp(3);
    restart.set_fast_exp(2);

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 9);
    trail.decide(bool_var(0));
    trail.propagate(bool_var(1), nullptr, 1);
    trail.decide(bool_var(2));
    trail.propagate(bool_var(3), nullptr, 2);

    auto learned = clause(lit(0), lit(2), lit(1), lit(3));

    restart.should_restart();

    restart.on_learned_clause(db, trail, learned);
    REQUIRE_THAT(restart.fast(), Catch::Matchers::WithinRel(2.f / 4));
    REQUIRE_THAT(restart.slow(), Catch::Matchers::WithinRel(2.f / 8));
}