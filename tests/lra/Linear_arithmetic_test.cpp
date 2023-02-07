#include <catch2/catch_test_macros.hpp>

#include "Clause.h"
#include "Linear_arithmetic.h"
#include "Literal.h"
#include "test.h"

namespace perun::test {

// propagate that lit is true in trail at current decision level without reason
auto propagate(Trail& trail, Literal lit)
{
    auto& model = trail.model<bool>(Variable::boolean);
    assert(!model.is_defined(lit.var().ord()));
    model.set_value(lit.var().ord(), !lit.is_negation());
    trail.propagate(lit.var(), nullptr, trail.decision_level());
}

// decide that lit is true in trail
auto decide(Trail& trail, Literal lit)
{
    auto& model = trail.model<bool>(Variable::boolean);
    assert(!model.is_defined(lit.var().ord()));
    model.set_value(lit.var().ord(), !lit.is_negation());
    trail.decide(lit.var());
}

template <typename Value> auto decide(Trail& trail, Linear_constraint<Value> const& cons)
{
    return decide(trail, cons.lit());
}

template <typename Value> auto propagate(Trail& trail, Linear_constraint<Value> const& cons)
{
    return propagate(trail, cons.lit());
}

} // namespace perun::test

TEST_CASE("Propagate in an empty trail", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 10);
    Linear_arithmetic lra;
    auto conflict = lra.propagate(db, trail);
    REQUIRE(!conflict);
    REQUIRE(trail.empty());
}

TEST_CASE("Propagate unit constraints on the trail", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto lin = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    // prepare test constraints on the trail
    propagate(trail, lin(x < 10));
    propagate(trail, lin(x >= 0));

    auto conflict = lra.propagate(db, trail);
    REQUIRE(!conflict);

    auto [lb, ub] = lra.find_bounds(models, x.ord());
    REQUIRE(lb.value() == 0);
    REQUIRE(ub.value() == 10);
}

TEST_CASE("Detect implied equality", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    // prepare test constraints on the trail
    propagate(trail, linear(x <= 4));
    propagate(trail, linear(x >= 4));
    propagate(trail, linear(y == 8));
    propagate(trail, linear(z != 16));

    REQUIRE(!models.owned().is_defined(x.ord()));
    REQUIRE(!models.owned().is_defined(y.ord()));
    REQUIRE(!models.owned().is_defined(z.ord()));

    auto conflict = lra.propagate(db, trail);
    REQUIRE(!conflict);

    REQUIRE(models.owned().is_defined(x.ord()));
    REQUIRE(models.owned().value(x.ord()) == 4);
    REQUIRE(trail.decision_level(x) == 0);

    REQUIRE(models.owned().is_defined(y.ord()));
    REQUIRE(models.owned().value(y.ord()) == 8);
    REQUIRE(trail.decision_level(y) == 0);

    REQUIRE(!models.owned().is_defined(z.ord()));
    REQUIRE(!trail.decision_level(z));
}

TEST_CASE("Recursively propagate unit constraints", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    propagate(trail, linear(x + y + z <= 4));
    propagate(trail, linear(x + y <= 8));
    propagate(trail, linear(x <= 16));
    propagate(trail, linear(y == 0));
    propagate(trail, linear(z == 0));

    auto conflict = lra.propagate(db, trail);
    REQUIRE(!conflict);

    auto [lb, ub] = lra.find_bounds(models, x.ord());
    REQUIRE(lb.value() == std::numeric_limits<Linear_arithmetic::Value_type>::lowest());
    REQUIRE(ub.value() == 4);
}

TEST_CASE("Propagate unit constraints over multiple decision levels", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    propagate(trail, linear(x + y + z <= 4));
    propagate(trail, linear(x + y <= 8));
    propagate(trail, linear(x <= 16));
    {
        auto conflict = lra.propagate(db, trail);
        REQUIRE(!conflict);

        auto [lb, ub] = lra.find_bounds(models, x.ord());
        REQUIRE(lb.value() == std::numeric_limits<Linear_arithmetic::Value_type>::lowest());
        REQUIRE(ub.value() == 16);
    }

    // make x + y <= 8 unit
    decide(trail, linear(y == 0));
    {
        auto conflict = lra.propagate(db, trail);
        REQUIRE(!conflict);

        auto [lb, ub] = lra.find_bounds(models, x.ord());
        REQUIRE(lb.value() == std::numeric_limits<Linear_arithmetic::Value_type>::lowest());
        REQUIRE(ub.value() == 8);
    }

    // make x + y + z <= 4 unit
    decide(trail, linear(z == 0));
    {
        auto conflict = lra.propagate(db, trail);
        REQUIRE(!conflict);

        auto [lb, ub] = lra.find_bounds(models, x.ord());
        REQUIRE(lb.value() == std::numeric_limits<Linear_arithmetic::Value_type>::lowest());
        REQUIRE(ub.value() == 4);
    }
}

TEST_CASE("LRA propagation is idempotent", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    propagate(trail, linear(x + y + z <= 4));
    propagate(trail, linear(x + y <= 8));
    propagate(trail, linear(x <= 16));
    propagate(trail, linear(y == 0));
    propagate(trail, linear(z == 0));

    REQUIRE(!lra.propagate(db, trail));
    REQUIRE(!lra.propagate(db, trail));
    REQUIRE(!lra.propagate(db, trail));

    REQUIRE(trail.assigned(trail.decision_level()).size() == 7);
    REQUIRE(!trail.decision_level(x));
    REQUIRE(trail.decision_level(y) == 0);
    REQUIRE(trail.decision_level(z) == 0);

    auto [lb, ub] = lra.find_bounds(models, x.ord());
    REQUIRE(lb.value() == std::numeric_limits<Linear_arithmetic::Value_type>::lowest());
    REQUIRE(ub.value() == 4);
}

TEST_CASE("Only propagate equality once if there are multiple sources", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    propagate(trail, linear(x + y == 4));
    propagate(trail, linear(x + z == 5));
    propagate(trail, linear(y == 0));
    propagate(trail, linear(z == 1));

    REQUIRE(!lra.propagate(db, trail));

    REQUIRE(trail.assigned(trail.decision_level()).size() == 7);
    REQUIRE(trail.decision_level(x) == 0);
    REQUIRE(trail.decision_level(y) == 0);
    REQUIRE(trail.decision_level(z) == 0);
}

TEST_CASE("Propagate fully assigned constraints in the system", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    // add a constraint that is not on the trail
    linear(x + y + z <= 0);
    propagate(trail, linear(x == 1));
    propagate(trail, linear(y == 0));
    propagate(trail, linear(z == 0));

    REQUIRE(!perun::eval(models.boolean(), linear(x + y + z <= 0).lit()));
    REQUIRE(!perun::eval(models.owned(), linear(x + y + z <= 0)));
    REQUIRE(!trail.decision_level(linear(x + y + z <= 0).lit().var()));

    REQUIRE(!lra.propagate(db, trail));

    REQUIRE(trail.decision_level(linear(x + y + z <= 0).lit().var()) == 0);
    REQUIRE(perun::eval(models.boolean(), linear(x + y + z <= 0).lit()) == false);
    REQUIRE(perun::eval(models.owned(), linear(x + y + z <= 0)) == false);
}

TEST_CASE("Compute bounds corretly after backtracking", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    decide(trail, linear(x <= 16));
    REQUIRE(!lra.propagate(db, trail));
    decide(trail, linear(x <= 8));
    REQUIRE(!lra.propagate(db, trail));
    decide(trail, linear(x <= 4));
    REQUIRE(!lra.propagate(db, trail));

    auto [lb, ub] = lra.find_bounds(models, x.ord());
    REQUIRE(lb.value() == std::numeric_limits<Linear_arithmetic::Value_type>::lowest());
    REQUIRE(ub.value() == 4);

    trail.backtrack(1);
    decide(trail, linear(x <= 12));
    REQUIRE(!lra.propagate(db, trail));

    std::tie(lb, ub) = lra.find_bounds(models, x.ord());
    REQUIRE(lb.value() == std::numeric_limits<Linear_arithmetic::Value_type>::lowest());
    REQUIRE(ub.value() == 12);
}

TEST_CASE("Detect a bound conflict", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    SECTION("with strict lower bound")
    {
        propagate(trail, linear(x <= y));
        propagate(trail, linear(z < x));
        propagate(trail, linear(y == 0));
        propagate(trail, linear(z == 0));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() == clause(-linear(z < x), -linear(x <= y), linear(z < y)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
        REQUIRE(perun::eval(models.owned(), linear(z < y)) == false);
    }

    SECTION("with strict upper bound")
    {
        propagate(trail, linear(x < y));
        propagate(trail, linear(z <= x));
        propagate(trail, linear(y == 0));
        propagate(trail, linear(z == 0));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() == clause(-linear(z <= x), -linear(x < y), linear(z < y)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
        REQUIRE(perun::eval(models.owned(), linear(z < y)) == false);
    }

    SECTION("with both bounds strict")
    {
        propagate(trail, linear(x < y));
        propagate(trail, linear(z < x));
        propagate(trail, linear(y == 0));
        propagate(trail, linear(z == 0));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() == clause(-linear(z < x), -linear(x < y), linear(z < y)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
        REQUIRE(perun::eval(models.owned(), linear(z < y)) == false);
    }

    SECTION("with non-strict bounds")
    {
        propagate(trail, linear(x <= y));
        propagate(trail, linear(z <= x));
        propagate(trail, linear(y == -1));
        propagate(trail, linear(z == 1));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() == clause(-linear(z <= x), -linear(x <= y), linear(z <= y)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
        REQUIRE(perun::eval(models.owned(), linear(z <= y)) == false);
    }

    SECTION("with only one variable")
    {
        propagate(trail, linear(x < 0));
        propagate(trail, linear(x > 1));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() == clause(-linear(1 < x), -linear(x < 0)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
    }

    SECTION("with two equalities")
    {
        propagate(trail, linear(x + y == 2));
        propagate(trail, linear(2 * x + 4 * y == 4));
        propagate(trail, linear(x == 0));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() == clause(-linear(x + y == 2), -linear(2 * x + 4 * y == 4), linear(x == 2)));
        REQUIRE(perun::eval(models.owned(), linear(x == 2)) == false);
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
    }
}

TEST_CASE("Detect trivial bound conflict with several variables", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 2);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 2);
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    decide(trail, linear(x - y > 1));
    decide(trail, linear(x - y < 1));
    decide(trail, linear(x == 0));
    auto conflict = lra.propagate(db, trail);
    REQUIRE(conflict);
    REQUIRE(conflict.value() == clause(-linear(x - y < 1), -linear(x - y > 1)));
}

TEST_CASE("Detect trivial inequality conflict with several variables", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 2);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 2);
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    decide(trail, linear(x - y >= 1));
    decide(trail, linear(x - y <= 1));
    decide(trail, linear(x - y != 1));
    decide(trail, linear(x == 0));
    auto conflict = lra.propagate(db, trail);
    REQUIRE(conflict);
    REQUIRE(conflict.value() == clause(-linear(x - y <= 1), -linear(x - y >= 1), linear(x - y == 1)));
}

TEST_CASE("Always choose a new boolean variable for unique derived constraints", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 1);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    lra.on_variable_resize(Variable::boolean, 1);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    propagate(trail, linear(y == 0));
    propagate(trail, linear(x > 0));
    propagate(trail, linear(x + y < 0));

    auto conflict = lra.propagate(db, trail);
    REQUIRE(conflict);
    REQUIRE(conflict.value() == clause(-linear(x > 0), -linear(x + y < 0), linear(y < 0)));
    REQUIRE(perun::eval(models.owned(), linear(y < 0)) == false);
    REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
    REQUIRE(linear(y < 0).lit().var().ord() == 4);
}

TEST_CASE("Detect an inequality conflict", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    SECTION("with non-trivial derivations")
    {
        propagate(trail, linear(y <= x));
        propagate(trail, linear(x <= z));
        propagate(trail, linear(x != 0));
        propagate(trail, linear(y == 0));
        propagate(trail, linear(z == 0));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() ==
                clause(-linear(y <= x), -linear(x <= z), linear(x == 0), linear(y < 0), linear(0 < z)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
        REQUIRE(perun::eval(models.owned(), linear(y < 0)) == false);
        REQUIRE(perun::eval(models.owned(), linear(0 < z)) == false);
    }

    SECTION("with both derived constraints trivial")
    {
        propagate(trail, linear(x <= 4));
        propagate(trail, linear(x >= 4));
        propagate(trail, linear(x != 4));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() ==
                clause(-linear(4 <= x), -linear(x <= 4), linear(x == 4)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
    }

    SECTION("with trivial derivation from upper bound")
    {
        propagate(trail, linear(x <= 4));
        propagate(trail, linear(x + y >= 4));
        propagate(trail, linear(x != 4));
        propagate(trail, linear(y == 0));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() ==
                clause(-linear(x + y >= 4), -linear(x <= 4), linear(x == 4), linear(y > 0)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
    }

    SECTION("with trivial derivation from lower bound")
    {
        propagate(trail, linear(x + y <= 4));
        propagate(trail, linear(x >= 4));
        propagate(trail, linear(x != 4));
        propagate(trail, linear(y == 0));

        auto conflict = lra.propagate(db, trail);
        REQUIRE(conflict);
        REQUIRE(conflict.value() ==
                clause(-linear(x >= 4), -linear(x + y <= 4), linear(x == 4), linear(y < 0)));
        REQUIRE(perun::eval(models.boolean(), conflict.value()) == false);
    }
}

TEST_CASE("Decide variable", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Linear_arithmetic::Value_type>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, trail.model<Linear_arithmetic::Value_type>(Variable::rational).num_vars());
    auto linear = factory(lra, trail);
    auto models = lra.relevant_models(trail);

    // variables to decide
    Variable x{0, Variable::rational};
    Variable y{1, Variable::rational};
    Variable z{2, Variable::rational};

    SECTION("decide 0 if possible")
    {
        propagate(trail, linear(y <= 10));
        propagate(trail, linear(y >= -10));
        lra.propagate(db, trail);

        lra.decide(db, trail, x);
        REQUIRE(trail.decision_level(x) == 1);
        REQUIRE(models.owned().is_defined(x.ord()));
        REQUIRE(models.owned().value(x.ord()) == 0);

        lra.decide(db, trail, y);
        REQUIRE(trail.decision_level(y) == 2);
        REQUIRE(models.owned().is_defined(y.ord()));
        REQUIRE(models.owned().value(y.ord()) == 0);
    }

    SECTION("decide a value within allowed range")
    {
        propagate(trail, linear(x <= 8));
        propagate(trail, linear(0 < x));
        propagate(trail, linear(x != 8));
        propagate(trail, linear(x != 4));
        propagate(trail, linear(x != 2));

        propagate(trail, linear(2 <= y));
        propagate(trail, linear(y <= 10));
        propagate(trail, linear(y != 10));

        propagate(trail, linear(-10 < z));
        propagate(trail, linear(z < -4));
        lra.propagate(db, trail);

        lra.decide(db, trail, x);
        REQUIRE(trail.decision_level(x) == 1);
        REQUIRE(models.owned().is_defined(x.ord()));
        REQUIRE(models.owned().value(x.ord()) < 8);
        REQUIRE(models.owned().value(x.ord()) > 0);
        REQUIRE(models.owned().value(x.ord()) != 4);
        REQUIRE(models.owned().value(x.ord()) != 2);

        lra.decide(db, trail, y);
        REQUIRE(trail.decision_level(y) == 2);
        REQUIRE(models.owned().is_defined(y.ord()));
        REQUIRE(models.owned().value(y.ord()) < 10);
        REQUIRE(models.owned().value(y.ord()) >= 2);

        lra.decide(db, trail, z);
        REQUIRE(trail.decision_level(z) == 3);
        REQUIRE(models.owned().is_defined(z.ord()));
        REQUIRE(models.owned().value(z.ord()) < -4);
        REQUIRE(models.owned().value(z.ord()) > -10);
    }

    SECTION("prefer integer values with a small absolute value")
    {
        propagate(trail, linear(x <= 100));
        propagate(trail, linear(x > 2));

        propagate(trail, linear(y > -8));
        propagate(trail, linear(y < 8));
        propagate(trail, linear(y != 0));
        propagate(trail, linear(y != 1));
        propagate(trail, linear(y != -1));
        propagate(trail, linear(y != -2));

        propagate(trail, linear(z < -5));
        propagate(trail, linear(z > -10));
        lra.propagate(db, trail);

        lra.decide(db, trail, x);
        REQUIRE(trail.decision_level(x) == 1);
        REQUIRE(models.owned().is_defined(x.ord()));
        REQUIRE(models.owned().value(x.ord()) == 3);

        lra.decide(db, trail, y);
        REQUIRE(trail.decision_level(y) == 2);
        REQUIRE(models.owned().is_defined(y.ord()));
        REQUIRE(models.owned().value(y.ord()) == 2);

        lra.decide(db, trail, z);
        REQUIRE(trail.decision_level(z) == 3);
        REQUIRE(models.owned().is_defined(z.ord()));
        REQUIRE(models.owned().value(z.ord()) == -6);
    }

    SECTION("decide value if there are no integer values allowed")
    {
        propagate(trail, linear(x < 1));
        propagate(trail, linear(x > 0));
        lra.propagate(db, trail);

        lra.decide(db, trail, x);
        REQUIRE(trail.decision_level(x) == 1);
        REQUIRE(models.owned().is_defined(x.ord()));
        REQUIRE(models.owned().value(x.ord()) < 1);
        REQUIRE(models.owned().value(x.ord()) > 0);
    }

    SECTION("decide integer value with negative lower bound and non-negative upper bound")
    {
        propagate(trail, linear(x < 0));
        lra.propagate(db, trail);

        lra.decide(db, trail, x);
        REQUIRE(trail.decision_level(x) == 1);
        REQUIRE(models.owned().is_defined(x.ord()));
        REQUIRE(models.owned().value(x.ord()) == -1);
    }

    SECTION("decide integer value with negative lower bound and negative upper bound")
    {
        propagate(trail, linear(x < -1));
        lra.propagate(db, trail);

        lra.decide(db, trail, x);
        REQUIRE(trail.decision_level(x) == 1);
        REQUIRE(models.owned().is_defined(x.ord()));
        REQUIRE(models.owned().value(x.ord()) == -2);
    }
}