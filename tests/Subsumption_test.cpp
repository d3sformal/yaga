#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Subsumption.h"

TEST_CASE("Remove subsumed learned clauses", "[subsumption]")
{
    using namespace yaga;
    using namespace yaga::test;

    Trail trail;

    Database db;
    db.learn_clause(lit(0), lit(1), lit(2));
    db.learn_clause(lit(1), lit(2), lit(3));
    db.learn_clause(lit(1), lit(2));

    Subsumption s;
    s.on_variable_resize(Variable::boolean, 4);
    s.on_restart(db, trail);

    REQUIRE(db.learned().size() == 1);
    REQUIRE(*db.learned().begin() == clause(lit(1), lit(2)));
}

TEST_CASE("Strengthen conflict clause", "[self-subsumption]")
{
    using namespace yaga;
    using namespace yaga::test;

    Database db;
    db.learn_clause(~lit(0), ~lit(1), lit(2));
    db.learn_clause(lit(1));

    Trail trail;
    auto& model = trail.set_model<bool>(Variable::boolean, 4);

    model.set_value(0, false);
    trail.propagate(bool_var(0), &*(db.learned().begin()), trail.decision_level());

    model.set_value(1, true);
    trail.propagate(bool_var(1), &*(db.learned().begin() + 1), trail.decision_level());

    model.set_value(2, true);
    trail.decide(bool_var(2));

    auto conflict = clause(lit(0), ~lit(1), lit(2), lit(3));

    Subsumption s;
    s.on_variable_resize(Variable::boolean, 4);
    s.minimize(trail, conflict);
    REQUIRE(conflict == clause(lit(2), lit(3)));
}