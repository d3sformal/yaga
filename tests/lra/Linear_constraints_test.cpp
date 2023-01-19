#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Fraction.h"
#include "Linear_constraints.h"

TEST_CASE("Create unit test instances using the test interface", "[test_expr]")
{
    using namespace perun;
    using namespace perun::test;

    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
    auto make = factory(repo);
    auto [x, y, z] = real_vars<3>();

    auto constraints = std::array{
        std::tuple{make(x < 1), Order_predicate::lt, false},
        std::tuple{make(x <= 1), Order_predicate::leq, false},
        std::tuple{make(x == 1), Order_predicate::eq, false},
        std::tuple{make(x > 1), Order_predicate::leq, true},
        std::tuple{make(x >= 1), Order_predicate::lt, true},
        std::tuple{make(x != 1), Order_predicate::eq, true},
    };

    for (auto [cons, exp_pred, exp_polarity] : constraints)
    {
        REQUIRE(std::ranges::equal(cons.vars(), std::vector<int>{x.ord()}));
        REQUIRE(std::ranges::equal(cons.coef(), std::vector<Value_type>{1}));
        REQUIRE(cons.pred() == exp_pred);
        REQUIRE(cons.rhs() == 1);
        REQUIRE(cons.lit().is_negation() == exp_polarity);
    }
    
    auto cons = make(2 * x < 4);
    REQUIRE(std::ranges::equal(cons.vars(), std::vector<int>{x.ord()}));
    REQUIRE(std::ranges::equal(cons.coef(), std::vector<Value_type>{1})); // normalized by Linear_constraints
    REQUIRE(cons.pred() == Order_predicate::lt);
    REQUIRE(cons.rhs() == 2);
    REQUIRE(!cons.lit().is_negation());
}

TEST_CASE("Create complicated predicates", "[test_expr]")
{
    using namespace perun;
    using namespace perun::test;

    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
    auto make = factory(repo);
    auto [x, y, z] = real_vars<3>();

    auto constraints = std::array{
        std::tuple{make(2 * x + 5 * y + 8 * z < x + y), Order_predicate::lt, false},
        std::tuple{make(2 * x + 5 * y + 8 * z <= x + y), Order_predicate::leq, false},
        std::tuple{make(2 * x + 5 * y + 8 * z == x + y), Order_predicate::eq, false},
        std::tuple{make(2 * x + 5 * y + 8 * z > x + y), Order_predicate::leq, true},
        std::tuple{make(2 * x + 5 * y + 8 * z >= x + y), Order_predicate::lt, true},
        std::tuple{make(2 * x + 5 * y + 8 * z != x + y), Order_predicate::eq, true},
    };

    for (auto [cons, exp_pred, exp_polarity] : constraints)
    {
        REQUIRE(std::ranges::equal(cons.vars(), std::vector<int>{x.ord(), y.ord(), z.ord()}));
        REQUIRE(std::ranges::equal(cons.coef(), std::vector<Value_type>{1, 4, 8}));
        REQUIRE(cons.pred() == exp_pred);
        REQUIRE(cons.rhs() == 0);
        REQUIRE(cons.lit().is_negation() == exp_polarity);
    }
}

TEST_CASE("Combine coefficients of variables", "[test_expr]")
{
    using namespace perun;
    using namespace perun::test;
    using namespace perun::literals;

    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
    auto make = factory(repo);
    auto [x, y, z, w] = real_vars<4>();

    auto cons = make(x + 2 * y + 3 * x + y + w <= x + y + z);

    REQUIRE(std::ranges::equal(cons.vars(), std::vector<int>{x.ord(), y.ord(), z.ord(), w.ord()}));
    REQUIRE(std::ranges::equal(cons.coef(), std::vector<Value_type>{1, 2_r / 3, -1_r / 3, 1_r / 3}));
    REQUIRE(cons.pred() == Order_predicate::leq);
    REQUIRE(cons.rhs() == 0);
    REQUIRE(!cons.lit().is_negation());
}

TEST_CASE("Create normalized constraints", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;
    using namespace perun::literals;

    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
    auto make = factory(repo);
    auto [x, y] = real_vars<2>();

    auto cons = make(x < 10);
    REQUIRE(std::ranges::equal(cons.vars(), std::vector{x.ord()}));
    REQUIRE(std::ranges::equal(cons.coef(), std::vector<Value_type>{1}));
    REQUIRE(cons.rhs() == 10);
    REQUIRE(cons.pred() == Order_predicate::lt);
    REQUIRE(cons.lit() == Literal{0});

    cons = make(2 * x + 3 * y <= -5);
    REQUIRE(std::ranges::equal(cons.vars(), std::vector{x.ord(), y.ord()}));
    REQUIRE(std::ranges::equal(cons.coef(), std::vector<Value_type>{1, 3_r / 2}));
    REQUIRE(cons.rhs() == -5_r / 2);
    REQUIRE(cons.pred() == Order_predicate::leq);
    REQUIRE(cons.lit() == Literal{1});
}

TEST_CASE("Deduplicate constraints", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;
    using namespace perun::literals;

    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
    auto make = factory(repo);
    auto [x, y, z, w] = real_vars<4>();

    SECTION("coefficient of the lowest variable is 1 after normalization")
    {
        auto cons = make(2 * y - 4 * x <= 8);
        REQUIRE(std::ranges::equal(cons.vars(), std::vector{x.ord(), y.ord()}));
        REQUIRE(std::ranges::equal(cons.coef(), std::vector<Value_type>{1, -1_r / 2}));
        REQUIRE(cons.rhs() == -2);
        REQUIRE(cons.pred() == Order_predicate::lt);
        REQUIRE(cons.lit() == Literal{0}.negate());

        auto cons2 = make(-y + 2 * x < -4);
        REQUIRE(cons.lit() == cons2.lit().negate());
        REQUIRE(std::ranges::equal(cons.vars(), cons2.vars()));
        REQUIRE(std::ranges::equal(cons.vars(), cons2.vars()));
        REQUIRE(cons.rhs() == cons2.rhs());
        REQUIRE(cons.pred() == cons2.pred());
    }

    SECTION("variables with 0 coefficients are removed")
    {
        auto cons = make(2 * x + y + 0 * w <= y + z + 8);
        REQUIRE(std::ranges::equal(cons.vars(), std::vector{x.ord(), z.ord()}));
        REQUIRE(std::ranges::equal(cons.coef(), std::vector<Value_type>{1, -1_r / 2}));
        REQUIRE(cons.rhs() == 4);
        REQUIRE(cons.pred() == Order_predicate::leq);
    }
}

TEST_CASE("Constraints with different right-hand-side are different", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;
    
    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
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
    
    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
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
    
    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
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
    
    using Value_type = Fraction<int>;

    Linear_constraints<Value_type> repo;
    auto make = factory(repo);
    auto [x, y, z] = real_vars<3>();
    auto cons = make(x >= y).negate();

    Model<Value_type> model;
    model.resize(3);
    REQUIRE(!perun::eval(model, cons));
    model.set_value(x.ord(), 0);
    REQUIRE(!perun::eval(model, cons));
    model.set_value(y.ord(), 0);
    REQUIRE(perun::eval(model, cons) == false);
    model.set_value(y.ord(), 1);
    REQUIRE(perun::eval(model, cons) == true);
}