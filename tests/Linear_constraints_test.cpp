#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Linear_constraints.h"

TEST_CASE("Create unit test instances using the test interface", "[test_expr]")
{
    using namespace perun;
    using namespace perun::test;

    Linear_constraints<double> repo;
    auto make = factory(repo);
    auto [x, y, z] = real_vars<3>();

    auto constraints = std::array{
        std::tuple{make(x < 1), Order_predicate::LT, false},
        std::tuple{make(x <= 1), Order_predicate::LEQ, false},
        std::tuple{make(x == 1), Order_predicate::EQ, false},
        std::tuple{make(x > 1), Order_predicate::LEQ, true},
        std::tuple{make(x >= 1), Order_predicate::LT, true},
        std::tuple{make(x != 1), Order_predicate::EQ, true},
    };

    for (auto [cons, exp_pred, exp_polarity] : constraints)
    {
        REQUIRE(std::ranges::equal(cons.vars(), std::vector<int>{x.ord()}));
        REQUIRE(std::ranges::equal(cons.coef(), std::vector<double>{1}));
        REQUIRE(cons.pred() == exp_pred);
        REQUIRE(cons.rhs() == 1);
        REQUIRE(cons.lit().is_negation() == exp_polarity);
    }
    
    auto cons = make(2 * x < 4);
    REQUIRE(std::ranges::equal(cons.vars(), std::vector<int>{x.ord()}));
    REQUIRE(std::ranges::equal(cons.coef(), std::vector<double>{1})); // normalized by Linear_constraints
    REQUIRE(cons.pred() == Order_predicate::LT);
    REQUIRE(cons.rhs() == 2);
    REQUIRE(!cons.lit().is_negation());
}

TEST_CASE("Create complicated predicates", "[test_expr]")
{
    using namespace perun;
    using namespace perun::test;

    Linear_constraints<double> repo;
    auto make = factory(repo);
    auto [x, y, z] = real_vars<3>();

    auto constraints = std::array{
        std::tuple{make(2 * x + 5 * y + 8 * z < x + y), Order_predicate::LT, false},
        std::tuple{make(2 * x + 5 * y + 8 * z <= x + y), Order_predicate::LEQ, false},
        std::tuple{make(2 * x + 5 * y + 8 * z == x + y), Order_predicate::EQ, false},
        std::tuple{make(2 * x + 5 * y + 8 * z > x + y), Order_predicate::LEQ, true},
        std::tuple{make(2 * x + 5 * y + 8 * z >= x + y), Order_predicate::LT, true},
        std::tuple{make(2 * x + 5 * y + 8 * z != x + y), Order_predicate::EQ, true},
    };

    for (auto [cons, exp_pred, exp_polarity] : constraints)
    {
        REQUIRE(std::ranges::equal(cons.vars(), std::vector<int>{x.ord(), y.ord(), z.ord()}));
        REQUIRE(std::ranges::equal(cons.coef(), std::vector<double>{1, 4, 8}));
        REQUIRE(cons.pred() == exp_pred);
        REQUIRE(cons.rhs() == 0);
        REQUIRE(cons.lit().is_negation() == exp_polarity);
    }
}

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

TEST_CASE("Evaluate negation of a linear constraint", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Linear_constraints<double> repo;
    auto make = factory(repo);
    auto [x, y, z] = real_vars<3>();
    auto cons = make(x >= y).negate();

    Model<double> model;
    model.resize(3);
    REQUIRE(!perun::eval(model, cons));
    model.set_value(x.ord(), 0);
    REQUIRE(!perun::eval(model, cons));
    model.set_value(y.ord(), 0);
    REQUIRE(perun::eval(model, cons) == false);
    model.set_value(y.ord(), 1);
    REQUIRE(perun::eval(model, cons) == true);
}