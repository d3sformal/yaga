#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_vector.hpp>

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

// decide that a real variable var is equal to a value val
auto decide(Trail& trail, Variable var, Rational value)
{
    auto& model = trail.model<Rational>(Variable::rational);
    assert(!model.is_defined(var.ord()));
    model.set_value(var.ord(), value);
    trail.decide(var);
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
    trail.set_model<Rational>(Variable::rational, 10);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 10);
    auto conflicts = lra.propagate(db, trail);
    REQUIRE(conflicts.empty());
    REQUIRE(trail.empty());
}

TEST_CASE("Propagate unit constraints on the trail", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto lin = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    // prepare test constraints on the trail
    propagate(trail, lin(x < 10));
    propagate(trail, lin(x >= 0));

    auto conflicts = lra.propagate(db, trail);
    REQUIRE(conflicts.empty());

    auto& bounds_x = lra.find_bounds(x.ord());
    REQUIRE(bounds_x.lower_bound(models)->value() == 0);
    REQUIRE(bounds_x.upper_bound(models)->value() == 10);
}

TEST_CASE("Propagate unit constraints over multiple decision levels", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    propagate(trail, linear(x + y + z <= 4));
    propagate(trail, linear(x + y <= 8));
    propagate(trail, linear(x <= 16));
    {
        auto conflicts = lra.propagate(db, trail);
        REQUIRE(conflicts.empty());

        auto bounds_x = lra.find_bounds(x.ord());
        REQUIRE(!bounds_x.lower_bound(models));
        REQUIRE(bounds_x.upper_bound(models)->value() == 16);
    }

    // make x + y <= 8 unit
    decide(trail, y, 0);
    {
        auto conflicts = lra.propagate(db, trail);
        REQUIRE(conflicts.empty());

        auto bounds_x = lra.find_bounds(x.ord());
        REQUIRE(!bounds_x.lower_bound(models));
        REQUIRE(bounds_x.upper_bound(models)->value() == 8);
    }

    // make x + y + z <= 4 unit
    decide(trail, z, 0);
    {
        auto conflicts = lra.propagate(db, trail);
        REQUIRE(conflicts.empty());

        auto& bounds_x = lra.find_bounds(x.ord());
        REQUIRE(!bounds_x.lower_bound(models));
        REQUIRE(bounds_x.upper_bound(models)->value() == 4);
    }
}

TEST_CASE("LRA propagation is idempotent", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    decide(trail, y, 0);
    propagate(trail, linear(x + y + z <= 4));
    propagate(trail, linear(x + y <= 8));
    propagate(trail, linear(x <= 16));
    propagate(trail, linear(z == 0));

    REQUIRE(lra.propagate(db, trail).empty());
    REQUIRE(lra.propagate(db, trail).empty());
    REQUIRE(lra.propagate(db, trail).empty());

    REQUIRE(trail.assigned(trail.decision_level()).size() == 5);
    REQUIRE(!trail.decision_level(x));
    REQUIRE(trail.decision_level(y) == 1);
    REQUIRE(!trail.decision_level(z));
}

TEST_CASE("Propagate fully assigned constraints in the system", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    // add a constraint that is not on the trail
    linear(x + y + z <= 0);

    decide(trail, x, 1);
    REQUIRE(lra.propagate(db, trail).empty());
    decide(trail, y, 0);
    REQUIRE(lra.propagate(db, trail).empty());

    REQUIRE(!perun::eval(models.boolean(), linear(x + y + z <= 0).lit()));
    REQUIRE(!perun::eval(models.owned(), linear(x + y + z <= 0)));
    REQUIRE(!trail.decision_level(linear(x + y + z <= 0).lit().var()));

    decide(trail, z, 0);
    REQUIRE(lra.propagate(db, trail).empty());

    REQUIRE(trail.decision_level(linear(x + y + z <= 0).lit().var()) == 3);
    REQUIRE(perun::eval(models.boolean(), linear(x + y + z <= 0).lit()) == false);
    REQUIRE(perun::eval(models.owned(), linear(x + y + z <= 0)) == false);
}

TEST_CASE("Compute bounds correctly after backtracking", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    decide(trail, linear(x <= 16));
    REQUIRE(lra.propagate(db, trail).empty());
    decide(trail, linear(x <= 8));
    REQUIRE(lra.propagate(db, trail).empty());
    decide(trail, linear(x <= 4));
    REQUIRE(lra.propagate(db, trail).empty());

    auto& bounds_x = lra.find_bounds(x.ord());
    REQUIRE(!bounds_x.lower_bound(models));
    REQUIRE(bounds_x.upper_bound(models)->value() == 4);

    lra.on_before_backtrack(db, trail, 1);
    trail.backtrack(1);
    decide(trail, linear(x <= 12));
    REQUIRE(lra.propagate(db, trail).empty());

    REQUIRE(!bounds_x.lower_bound(models));
    REQUIRE(bounds_x.upper_bound(models)->value() == 12);
}

TEST_CASE("Detect a bound conflict", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    SECTION("with lower bound implied by an equality")
    {
        decide(trail, y, -1);
        propagate(trail, linear(x == 0));
        propagate(trail, linear(x - y <= 0));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(x == 0), ~linear(x - y <= 0), linear(y >= 0))));
        REQUIRE(perun::eval(models.owned(), linear(y >= 0)) == false);
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    }

    SECTION("with upper bound implied by an equality")
    {
        decide(trail, x, 1);
        propagate(trail, linear(y == 0));
        propagate(trail, linear(x - y <= 0));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(x - y <= 0), ~linear(y == 0), linear(x <= 0))));
        REQUIRE(perun::eval(models.owned(), linear(x <= 0)) == false);
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    }

    SECTION("with a strict lower bound")
    {
        decide(trail, y, 0);
        REQUIRE(lra.propagate(db, trail).empty());

        decide(trail, z, 0);
        propagate(trail, linear(x <= y));
        propagate(trail, linear(z < x));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(z < x), ~linear(x <= y), linear(z < y))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
        REQUIRE(perun::eval(models.owned(), linear(z < y)) == false);
    }

    SECTION("with strict upper bound")
    {
        decide(trail, y, 0);
        REQUIRE(lra.propagate(db, trail).empty());

        decide(trail, z, 0);
        propagate(trail, linear(x < y));
        propagate(trail, linear(z <= x));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(z <= x), ~linear(x < y), linear(z < y))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
        REQUIRE(perun::eval(models.owned(), linear(z < y)) == false);
    }

    SECTION("with both bounds strict")
    {
        decide(trail, y, 0);
        REQUIRE(lra.propagate(db, trail).empty());

        decide(trail, z, 0);
        propagate(trail, linear(x < y));
        propagate(trail, linear(z < x));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(z < x), ~linear(x < y), linear(z < y))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
        REQUIRE(perun::eval(models.owned(), linear(z < y)) == false);
    }

    SECTION("with non-strict bounds")
    {
        decide(trail, y, -1);
        REQUIRE(lra.propagate(db, trail).empty());

        decide(trail, z, 1);
        propagate(trail, linear(x <= y));
        propagate(trail, linear(z <= x));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(z <= x), ~linear(x <= y), linear(z <= y))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
        REQUIRE(perun::eval(models.owned(), linear(z <= y)) == false);
    }

    SECTION("with only one variable")
    {
        propagate(trail, linear(x < 0));
        propagate(trail, linear(x > 1));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(1 < x), ~linear(x < 0))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    }

    SECTION("with two equalities")
    {
        decide(trail, x, 0);
        propagate(trail, linear(x + y == 2));
        propagate(trail, linear(2 * x + 4 * y == 4));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(x + y == 2), ~linear(2 * x + 4 * y == 4), linear(x == 2))));
        REQUIRE(perun::eval(models.owned(), linear(x == 2)) == false);
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    }
}

TEST_CASE("Detect trivial bound conflict with several variables", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 2);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 2);
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    decide(trail, linear(x - y > 1));
    decide(trail, linear(x - y < 1));
    decide(trail, x, 0);
    auto conflicts = lra.propagate(db, trail);
    REQUIRE(!conflicts.empty());
    REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
        clause(~linear(x - y < 1), ~linear(x - y > 1))));
}

TEST_CASE("Detect trivial inequality conflict with several variables", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 2);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 2);
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    decide(trail, linear(x - y >= 1));
    decide(trail, linear(x - y <= 1));
    decide(trail, linear(x - y != 1));
    decide(trail, x, 0);
    auto conflicts = lra.propagate(db, trail);
    REQUIRE(!conflicts.empty());
    REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(clause(
        ~linear(x - y <= 1), ~linear(x - y >= 1), linear(x - y == 1))));
}

TEST_CASE("Always choose a new boolean variable for unique derived constraints", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 1);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    lra.on_variable_resize(Variable::boolean, 1);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    decide(trail, y, 0);
    propagate(trail, linear(x > 0));
    propagate(trail, linear(x + y < 0));

    auto conflicts = lra.propagate(db, trail);
    REQUIRE(!conflicts.empty());
    REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
        clause(~linear(x > 0), ~linear(x + y < 0), linear(y < 0))));
    REQUIRE(perun::eval(models.owned(), linear(y < 0)) == false);
    REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    REQUIRE(linear(y < 0).lit().var().ord() == 3);
}

TEST_CASE("Detect an inequality conflict", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 3);
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    SECTION("with non-trivial derivations")
    {
        decide(trail, y, 0);
        REQUIRE(lra.propagate(db, trail).empty());

        decide(trail, z, 0);
        propagate(trail, linear(y <= x));
        propagate(trail, linear(x <= z));
        propagate(trail, linear(x != 0));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
                clause(~linear(y <= x), ~linear(x <= z), linear(x == 0), linear(y < 0), linear(0 < z))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
        REQUIRE(perun::eval(models.owned(), linear(y < 0)) == false);
        REQUIRE(perun::eval(models.owned(), linear(0 < z)) == false);
    }

    SECTION("with both derived constraints trivial")
    {
        propagate(trail, linear(x <= 4));
        propagate(trail, linear(x >= 4));
        propagate(trail, linear(x != 4));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
                clause(~linear(4 <= x), ~linear(x <= 4), linear(x == 4))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    }

    SECTION("with trivial derivation from upper bound")
    {
        decide(trail, y, 0);
        propagate(trail, linear(x <= 4));
        propagate(trail, linear(x + y >= 4));
        propagate(trail, linear(x != 4));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
                clause(~linear(x + y >= 4), ~linear(x <= 4), linear(x == 4), linear(y > 0))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    }

    SECTION("with trivial derivation from lower bound")
    {
        decide(trail, y, 0);
        propagate(trail, linear(x + y <= 4));
        propagate(trail, linear(x >= 4));
        propagate(trail, linear(x != 4));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
                clause(~linear(x >= 4), ~linear(x + y <= 4), linear(x == 4), linear(y < 0))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    }

    SECTION("with upper bound and lower bound implied by the same equality")
    {
        decide(trail, y, 0);
        propagate(trail, linear(x == 0));
        propagate(trail, linear(x + y != 0));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(x == 0), ~linear(x + y != 0), linear(y < 0), linear(y > 0))));
        REQUIRE(perun::eval(models.boolean(), conflicts.front()) == false);
    }
}

TEST_CASE("Backtrack-decide a constraint", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 2);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, trail.model<Rational>(Variable::rational).num_vars());
    auto models = lra.relevant_models(trail);
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    auto cons = linear(x + y <= 0);

    models.owned().set_value(x.ord(), 0);
    trail.decide(x);
    REQUIRE(lra.propagate(db, trail).empty());

    models.owned().set_value(y.ord(), 0);
    trail.decide(y);
    REQUIRE(lra.propagate(db, trail).empty());

    lra.on_before_backtrack(db, trail, 1);
    trail.backtrack(1);
    trail.propagate(cons.lit().var(), nullptr, trail.decision_level());
    models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());

    REQUIRE(lra.propagate(db, trail).empty());
}

TEST_CASE("Propagate derived bound constraint semantically only if it is not on the trail", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 2);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, trail.model<Rational>(Variable::rational).num_vars());
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    decide(trail, y, 2);
    propagate(trail, ~linear(y == 0));
    propagate(trail, linear(x == 0));
    propagate(trail, linear(x - y == 0));
    auto conflicts = lra.propagate(db, trail);
    REQUIRE(!conflicts.empty());
    REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
        clause(~linear(x - y == 0), ~linear(x == 0), linear(y == 0))));
}

TEST_CASE("Propagate derived inequality constraint semantically only if it is not an the trail", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 2);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, trail.model<Rational>(Variable::rational).num_vars());
    auto linear = factory(lra, trail);
    auto [x, y] = real_vars<2>();

    SECTION("in upper bound")
    {
        decide(trail, y, 1);
        propagate(trail, linear(y == 1));
        propagate(trail, ~linear(1 < y));
        propagate(trail, linear(x <= y));
        propagate(trail, linear(1 <= x));
        propagate(trail, linear(x != 1));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(1 <= x), ~linear(x <= y), ~linear(x != 1), linear(1 < y))));
    }

    SECTION("in lower bound")
    {
        decide(trail, y, 1);
        propagate(trail, ~linear(y < 1));
        propagate(trail, linear(y == 1));
        propagate(trail, linear(x <= 1));
        propagate(trail, linear(y <= x));
        propagate(trail, linear(x != 1));

        auto conflicts = lra.propagate(db, trail);
        REQUIRE(!conflicts.empty());
        REQUIRE_THAT(conflicts.front(), Catch::Matchers::UnorderedEquals(
            clause(~linear(y <= x), ~linear(x <= 1), ~linear(x != 1), linear(y < 1))));
    }
}

TEST_CASE("The first two unassigned variables in a derived constraint have the highest decision level", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, trail.model<Rational>(Variable::rational).num_vars());
    auto linear = factory(lra, trail);
    auto [x, y, z] = real_vars<3>();

    decide(trail, y, 1);
    REQUIRE(lra.propagate(db, trail).empty());

    decide(trail, z, 1);
    propagate(trail, linear(y < x));
    propagate(trail, linear(x < z));

    auto conflicts = lra.propagate(db, trail);
    REQUIRE(!conflicts.empty());
    REQUIRE(conflicts.front() == clause(~linear(y < x), ~linear(x < z), linear(y < z)));

    // backtrack, decide
    lra.on_before_backtrack(db, trail, 1);
    trail.backtrack(1);
    decide(trail, linear(y >= z));
    REQUIRE(lra.propagate(db, trail).empty());
}

TEST_CASE("Decide variable", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;
    using namespace perun::literals;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, 3);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, trail.model<Rational>(Variable::rational).num_vars());
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

    SECTION("decide value in a small interval close to 0") 
    {
        propagate(trail, linear(x > 1_r / 10));
        propagate(trail, linear(x < 2_r / 10));
        lra.propagate(db, trail);

        lra.decide(db, trail, x);
        REQUIRE(trail.decision_level(x) == 1);
        REQUIRE(models.owned().is_defined(x.ord()));
        REQUIRE(models.owned().value(x.ord()) > 1_r / 10);
        REQUIRE(models.owned().value(x.ord()) < 2_r / 10);
    }

    SECTION("decide value in a small interval close to 1") 
    {
        propagate(trail, linear(x > 8_r / 10));
        propagate(trail, linear(x < 9_r / 10));
        lra.propagate(db, trail);

        lra.decide(db, trail, x);
        REQUIRE(trail.decision_level(x) == 1);
        REQUIRE(models.owned().is_defined(x.ord()));
        REQUIRE(models.owned().value(x.ord()) > 8_r / 10);
        REQUIRE(models.owned().value(x.ord()) < 9_r / 10);
    }
}