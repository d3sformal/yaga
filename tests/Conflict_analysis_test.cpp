#include <catch2/catch_test_macros.hpp>

#include "Trail.h"
#include "Database.h"
#include "Conflict_analysis.h"
#include "test.h"

TEST_CASE("Resolve propagated literal", "[conflict_analysis]")
{
    using namespace yaga;
    using namespace yaga::test;

    Database db;
    db.assert_clause(lit(0), lit(1), lit(2));

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 10);

    trail.decide(bool_var(0));
    model.set_value(0, false);

    trail.decide(bool_var(1));
    model.set_value(1, false);

    trail.propagate(bool_var(2), &*db.asserted().begin(), trail.decision_level());
    model.set_value(2, true);

    Conflict_analysis analysis;

    auto [learned, level] = analysis.analyze(trail, clause(lit(0), lit(1), ~lit(2)));
    REQUIRE(level == 1);
    REQUIRE(learned == clause(lit(1), lit(0)));
}

TEST_CASE("Add literals to conflict during resolution", "[conflict_analysis]")
{
    using namespace yaga;
    using namespace yaga::test;

    Database db;
    db.assert_clause(lit(0), lit(1), ~lit(2));
    db.assert_clause(lit(0), lit(2), lit(3));

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 10);

    trail.decide(bool_var(0));
    model.set_value(0, false);

    trail.decide(bool_var(1));
    model.set_value(1, false);

    trail.propagate(bool_var(2), &*db.asserted().begin(), trail.decision_level());
    model.set_value(2, false);

    trail.propagate(bool_var(3), &*(db.asserted().begin() + 1), trail.decision_level());
    model.set_value(3, true);

    Conflict_analysis analysis;

    auto [learned, level] = analysis.analyze(trail, clause(lit(2), ~lit(3)));
    REQUIRE(level == 1);
    REQUIRE(learned == clause(lit(2), lit(0)));
}

TEST_CASE("Derive a unit conflict clause", "[conflict_analysis]")
{
    using namespace yaga;
    using namespace yaga::test;

    Database db;
    db.assert_clause(lit(0), lit(1));
    db.assert_clause(lit(0), lit(2));

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 10);

    trail.decide(bool_var(0));
    model.set_value(0, false);

    trail.propagate(bool_var(1), &*db.asserted().begin(), trail.decision_level());
    model.set_value(1, true);

    trail.propagate(bool_var(2), &*(db.asserted().begin() + 1), trail.decision_level());
    model.set_value(2, true);

    Conflict_analysis analysis;

    auto [learned, level] = analysis.analyze(trail, clause(~lit(1), ~lit(2)));
    REQUIRE(level == 0);
    REQUIRE(learned == clause(lit(0)));
}

TEST_CASE("Derive an empty clause", "[conflict_analysis]")
{
    using namespace yaga;
    using namespace yaga::test;

    Database db;
    db.assert_clause(lit(0));
    db.assert_clause(~lit(0), lit(1));
    db.assert_clause(~lit(0), ~lit(1), lit(2));

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 10);

    trail.propagate(bool_var(0), &*db.asserted().begin(), trail.decision_level());
    model.set_value(0, true);

    trail.propagate(bool_var(1), &*(db.asserted().begin() + 1), trail.decision_level());
    model.set_value(1, true);

    trail.propagate(bool_var(2), &*(db.asserted().begin() + 2), trail.decision_level());
    model.set_value(2, true);

    Conflict_analysis analysis;

    auto [learned, level] = analysis.analyze(trail, clause(~lit(2)));
    REQUIRE(level == -1);
    REQUIRE(learned == clause());
}

TEST_CASE("Derive a semantic split clause", "[conflict_analysis]")
{
    using namespace yaga;
    using namespace yaga::test;

    Database db;
    db.assert_clause(~lit(0), ~lit(1), lit(2));

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 10);

    trail.decide(bool_var(7));
    model.set_value(7, false);

    trail.propagate(bool_var(0), nullptr, trail.decision_level());
    model.set_value(0, true);

    trail.propagate(bool_var(1), nullptr, trail.decision_level());
    model.set_value(1, true);

    trail.propagate(bool_var(2), &*db.asserted().begin(), trail.decision_level());
    model.set_value(2, true);

    Conflict_analysis analysis;

    auto [learned, level] = analysis.analyze(trail, clause(~lit(0), ~lit(1), ~lit(2)));

    REQUIRE(level == 0);
    REQUIRE(learned == clause(~lit(0), ~lit(1)));
}