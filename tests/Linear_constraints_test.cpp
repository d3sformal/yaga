#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Linear_constraints.h"

TEST_CASE("Create normalized constraints", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Linear_constraints<double> repo;
    auto make = factory(repo);
    auto [x, y] = real_vars<2>();

    auto cons = make(x < 10);
    REQUIRE(std::ranges::equal(cons.vars(), std::vector{x.ord()}));
    REQUIRE(std::ranges::equal(cons.coef(), std::vector{1}));
    REQUIRE(cons.rhs() == 10.0);
    REQUIRE(cons.pred() == Order_predicate::LT);
    REQUIRE(cons.lit() == Literal{0});

    cons = make(2 * x + 3 * y <= -5);
    REQUIRE(std::ranges::equal(cons.vars(), std::vector{x.ord(), y.ord()}));
    REQUIRE(std::ranges::equal(cons.coef(), std::vector{1,       3.0 / 2}));
    REQUIRE(cons.rhs() == -5.0 / 2);
    REQUIRE(cons.pred() == Order_predicate::LEQ);
    REQUIRE(cons.lit() == Literal{1});
}

TEST_CASE("Deduplicate constraints", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Linear_constraints<double> repo;
    auto make = factory(repo);
    auto [x, y] = real_vars<2>();

    auto cons = make(-4 * x + 2 * y <= 8);
    // coefficient of the lowest variable is 1 after normalization
    REQUIRE(std::ranges::equal(cons.vars(), std::vector{x.ord(), y.ord()}));
    REQUIRE(std::ranges::equal(cons.coef(), std::vector{1.0,     -1.0 / 2}));
    REQUIRE(cons.rhs() == -2);
    REQUIRE(cons.pred() == Order_predicate::LT);
    REQUIRE(cons.lit() == Literal{0}.negate());

    auto cons2 = make(2 * x - y < -4);
    REQUIRE(cons.lit() == cons2.lit().negate());
    REQUIRE(std::ranges::equal(cons.vars(), cons2.vars()));
    REQUIRE(std::ranges::equal(cons.vars(), cons2.vars()));
    REQUIRE(cons.rhs() == cons2.rhs());
    REQUIRE(cons.pred() == cons2.pred());
}

TEST_CASE("Constraints with different right-hand-side are different", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Linear_constraints<double> repo;
    auto make = factory(repo);
    auto [x, y] = real_vars<2>();
    auto cons1 = make(-2 * x + 4 * y <= 8);
    auto cons2 = make(-2 * x + 4 * y <= 16);
    REQUIRE(cons1.lit().var() != cons2.lit().var());
}

TEST_CASE("Constraints with different predicate are different", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Linear_constraints<double> repo;
    auto make = factory(repo);
    auto [x, y] = real_vars<2>();
    auto cons1 = make(-2 * x + 4 * y <= 8);
    auto cons2 = make(-2 * x + 4 * y < 8);
    auto cons3 = make(-2 * x + 4 * y == 8);
    REQUIRE(cons1.lit().var() != cons2.lit().var());
    REQUIRE(cons2.lit().var() != cons3.lit().var());
    REQUIRE(cons1.lit().var() != cons3.lit().var());
}

TEST_CASE("Constraints with different nubmer of variables are different", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Linear_constraints<double> repo;
    auto make = factory(repo);
    auto [x, y, z] = real_vars<3>();
    auto cons1 = make(x <= 0);
    auto cons2 = make(x + y <= 0);
    auto cons3 = make(y + y + z <= 0);
    REQUIRE(cons1.lit().var() != cons2.lit().var());
    REQUIRE(cons2.lit().var() != cons3.lit().var());
    REQUIRE(cons1.lit().var() != cons3.lit().var());
}