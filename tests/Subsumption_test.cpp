#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Subsumption.h"

TEST_CASE("Remove subsumed learned clauses", "[subsumption]")
{
    using namespace perun;
    using namespace perun::test;

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