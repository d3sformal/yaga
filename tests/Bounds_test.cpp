#include <catch2/catch_test_macros.hpp>

#include "Bounds.h"
#include "test.h"

// compute inequality implied by a unit linear constraint
template<typename Value>
inline perun::Implied_value<Value> implied(perun::Model<Value> const& model, perun::Linear_constraint<Value>& cons)
{
    return {cons.implied_value(model) / cons.coef().front(), cons};
}

TEST_CASE("Add upper bounds", "[bounds]")
{
    using namespace perun;
    using namespace perun::test;

    Model<double> model;
    model.resize(10);
    model.set_value(1, 0.0);
    model.set_value(2, 0.0);
    model.set_value(3, 0.0);
    model.set_value(4, 0.0);
    Bounds<double> bounds;
    Linear_constraints<double> constraints;
    auto make = factory(constraints);
    auto [x, y, z, w, a] = real_vars<5>();

    REQUIRE(bounds.upper_bound(model).value() == std::numeric_limits<double>::max());
    REQUIRE(bounds.upper_bound(model).reason().empty());

    auto cons = make(x + y <= 7);
    bounds.add_upper_bound(model, implied(model, cons));
    REQUIRE(bounds.upper_bound(model).value() == 7);
    REQUIRE(bounds.upper_bound(model).reason().lit() == cons.lit());

    auto cons2 = make(x + z <= 8);
    bounds.add_upper_bound(model, implied(model, cons2));
    REQUIRE(bounds.upper_bound(model).value() == 7);
    REQUIRE(bounds.upper_bound(model).reason().lit() == cons.lit());

    auto cons3 = make(x + w <= 6);
    bounds.add_upper_bound(model, implied(model, cons3));
    REQUIRE(bounds.upper_bound(model).value() == 6);
    REQUIRE(bounds.upper_bound(model).reason().lit() == cons3.lit());

    auto cons4 = make(x + a < 6);
    bounds.add_upper_bound(model, implied(model, cons4));
    REQUIRE(bounds.upper_bound(model).value() == 6);
    REQUIRE(bounds.upper_bound(model).reason().lit() == cons4.lit());
}

TEST_CASE("Add lower bounds", "[bounds]")
{
    using namespace perun;
    using namespace perun::test;

    Model<double> model;
    model.resize(10);
    model.set_value(1, 0.0);
    model.set_value(2, 0.0);
    model.set_value(3, 0.0);
    model.set_value(4, 0.0);
    Bounds<double> bounds;
    Linear_constraints<double> constraints;
    auto make = factory(constraints);
    auto [x, y, z, w, a] = real_vars<5>();

    REQUIRE(bounds.lower_bound(model).value() == std::numeric_limits<double>::lowest());
    REQUIRE(bounds.lower_bound(model).reason().empty());

    auto cons = make(-x + y <= 7);
    bounds.add_lower_bound(model, implied(model, cons));
    REQUIRE(bounds.lower_bound(model).value() == -7);
    REQUIRE(bounds.lower_bound(model).reason().lit() == cons.lit());

    auto cons2 = make(-x + z <= 8);
    bounds.add_lower_bound(model, implied(model, cons2));
    REQUIRE(bounds.lower_bound(model).value() == -7);
    REQUIRE(bounds.lower_bound(model).reason().lit() == cons.lit());

    auto cons3 = make(-x + w <= 6);
    bounds.add_lower_bound(model, implied(model, cons3));
    REQUIRE(bounds.lower_bound(model).value() == -6);
    REQUIRE(bounds.lower_bound(model).reason().lit() == cons3.lit());

    auto cons4 = make(-x + a < 6);
    bounds.add_lower_bound(model, implied(model, cons4));
    REQUIRE(bounds.lower_bound(model).value() == -6);
    REQUIRE(bounds.lower_bound(model).reason().lit() == cons4.lit());
}

TEST_CASE("Get upper bound after backtracking", "[bounds]")
{
    using namespace perun;
    using namespace perun::test;

    Model<double> model;
    model.resize(10);
    Bounds<double> bounds;
    Linear_constraints<double> constraints;
    auto make = factory(constraints);

    auto x = real_var(0);
    auto y = real_var(1);
    auto z = real_var(2);
    auto w = real_var(3);

    // y = 0
    auto cons = make(x + y <= 10);
    model.set_value(y.ord(), 0.0);
    bounds.add_upper_bound(model, implied(model, cons));

    // z = 0
    auto cons2 = make(x + z <= 7);
    model.set_value(z.ord(), 0.0);
    bounds.add_upper_bound(model, implied(model, cons2));

    // w = 0
    auto cons3 = make(x + w <= 5);
    model.set_value(w.ord(), 0.0);
    bounds.add_upper_bound(model, implied(model, cons3));

    REQUIRE(bounds.upper_bound(model).value() == 5);
    REQUIRE(bounds.upper_bound(model).reason().lit() == cons3.lit());

    // backtrack to y = 0
    model.clear(w.ord());
    model.clear(z.ord());

    REQUIRE(bounds.upper_bound(model).value() == 10);
    REQUIRE(bounds.upper_bound(model).reason().lit() == cons.lit());

    // backtrack before y = 0
    model.clear(y.ord());

    REQUIRE(bounds.upper_bound(model).value() == std::numeric_limits<double>::max());
    REQUIRE(bounds.upper_bound(model).reason().empty());
}

TEST_CASE("Exclude values", "[bounds]")
{
    using namespace perun;
    using namespace perun::test;

    Model<double> model;
    model.resize(10);
    Bounds<double> bounds;
    Linear_constraints<double> constraints;
    auto make = factory(constraints);

    auto x = real_var(0);
    auto y = real_var(1);
    auto z = real_var(2);

    REQUIRE(bounds.is_allowed(model, 10));
    REQUIRE(bounds.is_allowed(model, 5));

    // y = 0
    auto cons = make(x + y != 10);
    model.set_value(y.ord(), 0);
    bounds.add_inequality(implied(model, cons));
    REQUIRE(!bounds.is_allowed(model, 10));
    REQUIRE(bounds.is_allowed(model, 5));

    // z = 0
    auto cons2 = make(x + z != 5);
    model.set_value(z.ord(), 0);
    bounds.add_inequality(implied(model, cons2));
    REQUIRE(!bounds.is_allowed(model, 10));
    REQUIRE(!bounds.is_allowed(model, 5));

    // backtrack to y = 0
    model.clear(z.ord());
    REQUIRE(!bounds.is_allowed(model, 10));
    REQUIRE(bounds.is_allowed(model, 5));

    // backtrack before y = 0
    model.clear(y.ord());
    REQUIRE(bounds.is_allowed(model, 10));
    REQUIRE(bounds.is_allowed(model, 5));
}