#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Solver.h"
#include "Evsids.h"
#include "Bool_theory.h"

TEST_CASE("Check a satisfiable boolean formula", "[sat][integration]")
{
    using namespace perun;
    using namespace perun::test;

    Solver solver;
    solver.set_theory<Bool_theory>();
    solver.set_variable_order<Evsids>();
    solver.set_restart_policy<No_restart>();
    solver.trail().set_model<bool>(Variable::boolean, 3);
    solver.db().assert_clause(lit(0), lit(1), lit(2));
    solver.db().assert_clause(lit(0), lit(1), -lit(2));
    //solver.db().assert_clause(lit(0), -lit(1), lit(2));
    solver.db().assert_clause(lit(0), -lit(1), -lit(2));
    solver.db().assert_clause(-lit(0), lit(1), lit(2));
    solver.db().assert_clause(-lit(0), lit(1), -lit(2));
    solver.db().assert_clause(-lit(0), -lit(1), lit(2));
    solver.db().assert_clause(-lit(0), -lit(1), -lit(2));

    auto result = solver.check();
    REQUIRE(result == Solver::sat);

    auto& model = solver.trail().model<bool>(Variable::boolean);
    REQUIRE(model.is_defined(0));
    REQUIRE(model.value(0) == false);
    REQUIRE(model.is_defined(1));
    REQUIRE(model.value(1) == true);
    REQUIRE(model.is_defined(2));
    REQUIRE(model.value(2) == false);
}

TEST_CASE("Check an unsatisfiable boolean formula", "[unsat][integration]")
{
    using namespace perun;
    using namespace perun::test;

    Solver solver;
    solver.set_theory<Bool_theory>();
    solver.set_variable_order<Evsids>();
    solver.set_restart_policy<No_restart>();
    solver.trail().set_model<bool>(Variable::boolean, 3);
    solver.db().assert_clause(lit(0), lit(1), lit(2));
    solver.db().assert_clause(lit(0), lit(1), -lit(2));
    solver.db().assert_clause(lit(0), -lit(1), lit(2));
    solver.db().assert_clause(lit(0), -lit(1), -lit(2));
    solver.db().assert_clause(-lit(0), lit(1), lit(2));
    solver.db().assert_clause(-lit(0), lit(1), -lit(2));
    solver.db().assert_clause(-lit(0), -lit(1), lit(2));
    solver.db().assert_clause(-lit(0), -lit(1), -lit(2));

    auto result = solver.check();
    REQUIRE(result == Solver::unsat);
}