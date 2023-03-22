#include <catch2/catch_test_macros.hpp>

#include "Bounds.h"
#include "test.h"

// compute inequality implied by a unit linear constraint
template<typename Value>
inline perun::Implied_value<Value> implied(perun::Theory_models<Value> const& models, 
                                           perun::Linear_constraint<Value>& cons, int level)
{
    return {cons.vars().front(), cons.implied_value(models.owned()) / cons.coef().front(), 
            cons, models, level};
}

TEST_CASE("Validity of bounds depends on theory models", "[bounds]")
{
    using namespace perun;
    using namespace perun::test;

    using Value_type = Fraction<int>;

    Model<bool> bool_model;
    Model<Value_type> lra_model;
    bool_model.resize(10);
    lra_model.resize(5);
    Theory_models<Value_type> models{bool_model, lra_model};
    Bounds<Value_type> bounds;
    Linear_constraints<Value_type> constraints;
    auto make = factory(constraints);
    auto [x, y, z, w, a] = real_vars<5>();

    SECTION("Check allowed values with an empty bounds object")
    {
        REQUIRE(bounds.is_allowed(models, 0));
        REQUIRE(bounds.is_allowed(models, 1));
        REQUIRE(bounds.is_allowed(models, -1));
        REQUIRE(bounds.is_allowed(models, std::numeric_limits<int>::max()));
        REQUIRE(bounds.is_allowed(models, std::numeric_limits<int>::lowest()));
    }

    SECTION("Push new upper bounds to a stack")
    {
        std::array trail{
            make(x + y <= 7),
            make(x + z <= 8),
            make(x + w <= 6),
            make(x + a < 6),
        };
        for (auto const& cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        REQUIRE(!bounds.upper_bound(models));

        models.owned().set_value(y.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[0], 0));
        REQUIRE(bounds.upper_bound(models)->value() == 7);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[0].lit());

        models.owned().set_value(z.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[1], 1));
        REQUIRE(bounds.upper_bound(models)->value() == 7);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[0].lit());

        models.owned().set_value(w.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[2], 2));
        REQUIRE(bounds.upper_bound(models)->value() == 6);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[2].lit());

        models.owned().set_value(a.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[3], 3));
        REQUIRE(bounds.upper_bound(models)->value() == 6);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[3].lit());
    }

    SECTION("Push new lower bounds to a stack")
    {
        std::array trail{
            make(x + y >= -7),
            make(x + z >= -8),
            make(x + w >= -6),
            make(x + a > -6),
        };
        for (auto const& cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        REQUIRE(!bounds.lower_bound(models));

        models.owned().set_value(y.ord(), 0);
        bounds.add_lower_bound(models, implied(models, trail[0], 0));
        REQUIRE(bounds.lower_bound(models)->value() == -7);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[0].lit());

        models.owned().set_value(z.ord(), 0);
        bounds.add_lower_bound(models, implied(models, trail[1], 1));
        REQUIRE(bounds.lower_bound(models)->value() == -7);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[0].lit());

        models.owned().set_value(w.ord(), 0);
        bounds.add_lower_bound(models, implied(models, trail[2], 2));
        REQUIRE(bounds.lower_bound(models)->value() == -6);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[2].lit());

        models.owned().set_value(a.ord(), 0);
        bounds.add_lower_bound(models, implied(models, trail[3], 3));
        REQUIRE(bounds.lower_bound(models)->value() == -6);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[3].lit());
    }

    SECTION("Get upper bounds after backtracking an assignment of LRA variables")
    {
        std::array trail{
            make(x + y <= 10),
            make(x + z <= 7),
            make(x + w <= 5),
        };
        for (auto const& cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        // y = 0
        models.owned().set_value(y.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[0], 0));

        // z = 0
        models.owned().set_value(z.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[1], 0));

        // w = 0
        models.owned().set_value(w.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[2], 2));

        REQUIRE(bounds.upper_bound(models)->value() == 5);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[2].lit());

        // backtrack to y = 0
        models.owned().clear(w.ord());
        models.owned().clear(z.ord());

        REQUIRE(bounds.upper_bound(models)->value() == 10);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[0].lit());

        // backtrack before y = 0
        models.owned().clear(y.ord());

        REQUIRE(!bounds.upper_bound(models));
    }

    SECTION("Get upper bound after changing value of an LRA variable")
    {
        auto cons = make(x + y <= 8);
        models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());

        models.owned().set_value(y.ord(), 0);
        bounds.add_upper_bound(models, implied(models, cons, 1));

        REQUIRE(bounds.upper_bound(models)->value() == 8);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == cons.lit());

        models.owned().set_value(y.ord(), -2);
        bounds.add_upper_bound(models, implied(models, cons, 1));

        REQUIRE(bounds.upper_bound(models)->value() == 10);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == cons.lit());
    }

    SECTION("Get upper bounds after backtracking boolean variables")
    {
        std::array trail{
            make(x <= 10),
            make(x <= 7),
            make(x <= 5),
        };
        int level = 0;
        for (auto& cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
            bounds.add_upper_bound(models, implied(models, cons, ++level));
        }

        REQUIRE(bounds.upper_bound(models)->value() == 5);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[2].lit());

        models.boolean().clear(trail[2].lit().var().ord());
        models.boolean().clear(trail[1].lit().var().ord());
        
        REQUIRE(bounds.upper_bound(models)->value() == 10);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[0].lit());
    }

    SECTION("Get bounds after backtracking negation of the bound")
    {
        auto cons = make(x <= 0);
        auto not_cons = cons.negate();
        models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());

        bounds.add_upper_bound(models, implied(models, cons, 1));
        REQUIRE(bounds.upper_bound(models)->value() == 0);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == cons.lit());
        REQUIRE(!bounds.lower_bound(models));

        models.boolean().set_value(not_cons.lit().var().ord(), !not_cons.lit().is_negation());
        bounds.add_lower_bound(models, implied(models, not_cons, 1));

        REQUIRE(!bounds.upper_bound(models));
        REQUIRE(bounds.lower_bound(models)->value() == 0);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == not_cons.lit());
    }

    SECTION("Exclude values")
    {
        std::array trail{
            make(x + y != 10),
            make(x + z != 5),
        };
        for (auto const& cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        REQUIRE(!bounds.inequality(models, 10));
        REQUIRE(!bounds.inequality(models, 5));

        // y = 0
        models.owned().set_value(y.ord(), 0);
        bounds.add_inequality(implied(models, trail[0], 0));
        REQUIRE(bounds.inequality(models, 10));
        REQUIRE(!bounds.inequality(models, 5));

        // z = 0
        models.owned().set_value(z.ord(), 0);
        bounds.add_inequality(implied(models, trail[1], 1));
        REQUIRE(bounds.inequality(models, 10));
        REQUIRE(bounds.inequality(models, 5));

        // backtrack to y = 0
        models.owned().clear(z.ord());
        REQUIRE(bounds.inequality(models, 10));
        REQUIRE(!bounds.inequality(models, 5));

        // backtrack before y = 0
        models.owned().clear(y.ord());
        REQUIRE(!bounds.inequality(models, 10));
        REQUIRE(!bounds.inequality(models, 5));
    }

    SECTION("Backtrack excluded values")
    {
        std::array trail{
            make(x + y != 10),
            make(x + z != 10),
        };
        for (auto const& cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        REQUIRE(!bounds.inequality(models, 10));

        // y = 0
        models.owned().set_value(y.ord(), 0);
        bounds.add_inequality(implied(models, trail[0], 0));
        REQUIRE(bounds.inequality(models, 10)->reason().lit() == trail[0].lit());
        REQUIRE(bounds.inequality(models, 10)->value() == 10);

        // z = 0
        models.owned().set_value(z.ord(), 0);
        bounds.add_inequality(implied(models, trail[1], 1));
        REQUIRE(bounds.inequality(models, 10)->reason().lit() == trail[0].lit());

        // clear y
        models.owned().clear(y.ord());
        REQUIRE(bounds.inequality(models, 10)->reason().lit() == trail[1].lit());

        // clear z
        models.owned().clear(z.ord());
        REQUIRE(!bounds.inequality(models, 10));
    }
}

TEST_CASE("Add deduced bounds", "[bounds]")
{
    using namespace perun;
    using namespace perun::test;

    using Rational = Fraction<int>;

    constexpr int num_vars = 3;

    Model<bool> bool_model;
    Model<Rational> lra_model;
    bool_model.resize(10);
    lra_model.resize(num_vars);
    Theory_models<Rational> models{bool_model, lra_model};
    Linear_constraints<Rational> constraints;
    std::array<Bounds<Rational>, num_vars> bounds;
    auto make = factory(constraints);
    auto [x, y, z] = real_vars<num_vars>();

    SECTION("upper bound")
    {
        models.owned().set_value(z.ord(), 0);

        std::array trail{
            make(y + z > 0),
            make(x + y <= 0)
        };
        for (auto cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        std::vector deps{Implied_value<Rational>{y.ord(), 0, trail[0], models, 1}};
        bounds[y.ord()].add_lower_bound(models, {y.ord(), 0, trail[0], models, 1});
        bounds[x.ord()].add_upper_bound(models, {x.ord(), 0, trail[1], models, 1, deps});
        REQUIRE(!bounds[x.ord()].check_upper_bound(models, 0));
        REQUIRE(bounds[x.ord()].check_upper_bound(models, -1));
    }

    SECTION("lower bound")
    {
        models.owned().set_value(z.ord(), 0);

        std::array trail{
            make(y + z < 0),
            make(x + y >= 0)
        };
        for (auto cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        std::vector deps{Implied_value<Rational>{y.ord(), 0, trail[0], models, 1}};
        bounds[y.ord()].add_upper_bound(models, {y.ord(), 0, trail[0], models, 1});
        bounds[x.ord()].add_lower_bound(models, {x.ord(), 0, trail[1], models, 1, deps});
        REQUIRE(!bounds[x.ord()].check_lower_bound(models, 0));
        REQUIRE(bounds[x.ord()].check_lower_bound(models, 1));
    }
}

TEST_CASE("Add a bound retroactively", "[bounds]")
{
    using namespace perun;
    using namespace perun::test;

    using Value_type = Fraction<int>;

    Model<bool> bool_model;
    Model<Value_type> lra_model;
    bool_model.resize(10);
    lra_model.resize(6);
    Theory_models<Value_type> models{bool_model, lra_model};
    Bounds<Value_type> bounds;
    Linear_constraints<Value_type> constraints;
    auto make = factory(constraints);
    auto [x, y, z, w, a, b] = real_vars<6>();

    SECTION("upper bound")
    {
        std::array trail{
            make(x + y <= 9),
            make(x + z <= 8),
            make(x + w <= 6),
            make(x + a < 6),
            make(x + b < 6)
        };
        for (auto& cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        models.owned().set_value(y.ord(), 0);
        models.owned().set_value(z.ord(), 0);
        models.owned().set_value(w.ord(), 0);
        models.owned().set_value(a.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[0], 1));
        bounds.add_upper_bound(models, implied(models, trail[1], 2));
        bounds.add_upper_bound(models, implied(models, trail[2], 3));
        bounds.add_upper_bound(models, implied(models, trail[3], 4));

        REQUIRE(bounds.upper_bound(models)->value() == 6);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[3].lit());

        // propagate b = 0 at level 2
        models.owned().set_value(b.ord(), 0);
        bounds.add_upper_bound(models, implied(models, trail[4], 2));
        REQUIRE(bounds.upper_bound(models)->value() == 6);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[4].lit());

        // backtrack to level 3
        models.owned().clear(a.ord());
        REQUIRE(bounds.upper_bound(models)->value() == 6);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[4].lit());

        // backtrack to level 2
        models.owned().clear(w.ord());
        REQUIRE(bounds.upper_bound(models)->value() == 6);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[4].lit());

        // backtrack to level 1
        models.owned().clear(b.ord());
        models.owned().clear(z.ord());
        REQUIRE(bounds.upper_bound(models)->value() == 9);
        REQUIRE(bounds.upper_bound(models)->reason().lit() == trail[0].lit());

        // backtrack to level 0
        models.owned().clear(y.ord());
        REQUIRE(!bounds.upper_bound(models));
    }

    SECTION("lower bound")
    {
        std::array trail{
            make(x + y >= -9),
            make(x + z >= -8),
            make(x + w >= -6),
            make(x + a > -6),
            make(x + b > -6)
        };
        for (auto& cons : trail)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }

        models.owned().set_value(y.ord(), 0);
        models.owned().set_value(z.ord(), 0);
        models.owned().set_value(w.ord(), 0);
        models.owned().set_value(a.ord(), 0);
        bounds.add_lower_bound(models, implied(models, trail[0], 1));
        bounds.add_lower_bound(models, implied(models, trail[1], 2));
        bounds.add_lower_bound(models, implied(models, trail[2], 3));
        bounds.add_lower_bound(models, implied(models, trail[3], 4));

        REQUIRE(bounds.lower_bound(models)->value() == -6);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[3].lit());

        // propagate b = 0 at level 2
        models.owned().set_value(b.ord(), 0);
        bounds.add_lower_bound(models, implied(models, trail[4], 2));
        REQUIRE(bounds.lower_bound(models)->value() == -6);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[4].lit());

        // backtrack to level 3
        models.owned().clear(a.ord());
        REQUIRE(bounds.lower_bound(models)->value() == -6);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[4].lit());

        // backtrack to level 2
        models.owned().clear(w.ord());
        REQUIRE(bounds.lower_bound(models)->value() == -6);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[4].lit());

        // backtrack to level 1
        models.owned().clear(b.ord());
        models.owned().clear(z.ord());
        REQUIRE(bounds.lower_bound(models)->value() == -9);
        REQUIRE(bounds.lower_bound(models)->reason().lit() == trail[0].lit());

        // backtrack to level 0
        models.owned().clear(y.ord());
        REQUIRE(!bounds.lower_bound(models));
    }
}