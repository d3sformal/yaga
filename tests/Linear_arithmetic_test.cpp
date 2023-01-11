#include <catch2/catch_test_macros.hpp>

#include "test.h"
#include "Linear_arithmetic.h"
#include "Clause.h"
#include "Literal.h"

namespace perun::test {

    // create a linear constraint and return its literal
    auto factory(Linear_arithmetic& plugin)
    {
        return [plugin_ptr = &plugin](Linear_predicate const& pred) 
        {
            auto cons = plugin_ptr->constraint(pred.lhs.vars, pred.lhs.coef, pred.pred, pred.rhs);
            return pred.is_negation ? cons.negate() : cons;
        };
    }

    // decide that lit is true in trail
    auto decide(Trail& trail, Literal lit)
    {
        auto& model = trail.model<bool>(Variable::boolean);
        assert(!model.is_defined(lit.var().ord()));
        model.set_value(lit.var().ord(), !lit.is_negation());
        trail.decide(lit.var());
    }

    // propagate that lit is true in trail at current decision level without reason
    auto propagate(Trail& trail, Literal lit)
    {
        auto& model = trail.model<bool>(Variable::boolean);
        assert(!model.is_defined(lit.var().ord()));
        model.set_value(lit.var().ord(), !lit.is_negation());
        trail.propagate(lit.var(), nullptr, trail.decision_level());
    }

    template<typename Value>
    auto decide(Trail& trail, Linear_constraint<Value> const& cons)
    {
        return decide(trail, cons.lit());
    }

    template<typename Value>
    auto propagate(Trail& trail, Linear_constraint<Value> const& cons)
    {
        return propagate(trail, cons.lit());
    }
}

TEST_CASE("Propagate in an empty trail", "[linear_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<double>(Variable::rational, 10);
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
    trail.set_model<bool>(Variable::boolean, 10);
    auto& lra_model = trail.set_model<double>(Variable::rational, 10);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 10);
    auto lin = factory(lra);
    auto [x, y, z] = real_vars<3>();

    // prepare test constraints on the trail
    propagate(trail, lin(x < 10));
    propagate(trail, lin(x >= 0));

    auto conflict = lra.propagate(db, trail);
    REQUIRE(!conflict);

    auto [lb, ub] = lra.find_bounds(lra_model, x.ord());
    REQUIRE(lb.value() == 0);
    REQUIRE(ub.value() == 10);
}

TEST_CASE("Detect implied equality", "[lienar_arithmetic]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 10);
    auto& lra_model = trail.set_model<double>(Variable::rational, 10);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 10);
    auto linear = factory(lra);
    auto [x, y, z] = real_vars<3>();

    // prepare test constraints on the trail
    propagate(trail, linear(x <= 4));
    propagate(trail, linear(x >= 4));
    propagate(trail, linear(y == 8));
    propagate(trail, linear(z != 16));

    REQUIRE(!lra_model.is_defined(x.ord()));
    REQUIRE(!lra_model.is_defined(y.ord()));
    REQUIRE(!lra_model.is_defined(z.ord()));

    auto conflict = lra.propagate(db, trail);
    REQUIRE(!conflict);

    REQUIRE(lra_model.is_defined(x.ord()));
    REQUIRE(lra_model.value(x.ord()) == 4);
    REQUIRE(trail.decision_level(x) == 0);
    
    REQUIRE(lra_model.is_defined(y.ord()));
    REQUIRE(lra_model.value(y.ord()) == 8);
    REQUIRE(trail.decision_level(y) == 0);

    REQUIRE(!lra_model.is_defined(z.ord()));
    REQUIRE(!trail.decision_level(z));
}

TEST_CASE("Recursively propagate unit constraints", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 10);
    auto& lra_model = trail.set_model<double>(Variable::rational, 10);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 10);
    auto linear = factory(lra);
    auto [x, y, z] = real_vars<3>();

    propagate(trail, linear(x + y + z <= 4));
    propagate(trail, linear(x + y <= 8));
    propagate(trail, linear(x <= 16));
    propagate(trail, linear(y == 0));
    propagate(trail, linear(z == 0));

    auto conflict = lra.propagate(db, trail);
    REQUIRE(!conflict);

    auto [lb, ub] = lra.find_bounds(lra_model, x.ord());
    REQUIRE(lb.value() == std::numeric_limits<double>::lowest());
    REQUIRE(ub.value() == 4);
}

TEST_CASE("Propagate unit constraints over multiple decision levels", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 10);
    auto& lra_model = trail.set_model<double>(Variable::rational, 10);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 10);
    auto linear = factory(lra);
    auto [x, y, z] = real_vars<3>();

    propagate(trail, linear(x + y + z <= 4));
    propagate(trail, linear(x + y <= 8));
    propagate(trail, linear(x <= 16));
    {
        auto conflict = lra.propagate(db, trail);
        REQUIRE(!conflict);

        auto [lb, ub] = lra.find_bounds(lra_model, x.ord());
        REQUIRE(lb.value() == std::numeric_limits<double>::lowest());
        REQUIRE(ub.value() == 16);
    }

    // make x + y <= 8 unit
    decide(trail, linear(y == 0));
    {
        auto conflict = lra.propagate(db, trail);
        REQUIRE(!conflict);

        auto [lb, ub] = lra.find_bounds(lra_model, x.ord());
        REQUIRE(lb.value() == std::numeric_limits<double>::lowest());
        REQUIRE(ub.value() == 8);
    }

    // make x + y + z <= 4 unit
    decide(trail, linear(z == 0));
    {
        auto conflict = lra.propagate(db, trail);
        REQUIRE(!conflict);

        auto [lb, ub] = lra.find_bounds(lra_model, x.ord());
        REQUIRE(lb.value() == std::numeric_limits<double>::lowest());
        REQUIRE(ub.value() == 4);
    }
}

TEST_CASE("LRA propagation is idempotent", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    trail.set_model<bool>(Variable::boolean, 10);
    auto& lra_model = trail.set_model<double>(Variable::rational, 10);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 10);
    auto linear = factory(lra);
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

    auto [lb, ub] = lra.find_bounds(lra_model, x.ord());
    REQUIRE(lb.value() == std::numeric_limits<double>::lowest());
    REQUIRE(ub.value() == 4);
}

TEST_CASE("Propagate fully assigned constraints in the system", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    auto& bool_model = trail.set_model<bool>(Variable::boolean, 10);
    auto& lra_model = trail.set_model<double>(Variable::rational, 10);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 10);
    auto linear = factory(lra);
    auto [x, y, z] = real_vars<3>();

    // add a constraint that is not on the trail
    linear(x + y + z <= 0);
    propagate(trail, linear(x == 1));
    propagate(trail, linear(y == 0));
    propagate(trail, linear(z == 0));

    REQUIRE(!perun::eval(bool_model, linear(x + y + z <= 0).lit()));
    REQUIRE(!perun::eval(lra_model, linear(x + y + z <= 0)));

    REQUIRE(!lra.propagate(db, trail));

    REQUIRE(perun::eval(bool_model, linear(x + y + z <= 0).lit()) == false);
    REQUIRE(perun::eval(lra_model, linear(x + y + z <= 0)) == false);
}

TEST_CASE("Detect a bound conflict", "[linear_constraints]")
{
    using namespace perun;
    using namespace perun::test;

    Database db;
    Trail trail;
    auto& bool_model = trail.set_model<bool>(Variable::boolean, 10);
    auto& lra_model = trail.set_model<double>(Variable::rational, 10);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, 10);
    auto linear = factory(lra);
    auto [x, y, z] = real_vars<3>();

    propagate(trail, linear(x + y <= 0));
    propagate(trail, linear(x + z > 0));
    propagate(trail, linear(y == 0));
    propagate(trail, linear(z == 0));

    auto conflict = lra.propagate(db, trail);
    REQUIRE(conflict);
    REQUIRE(conflict.value() == clause(-linear(x + z > 0), -linear(x + y <= 0), linear(y - z < 0)));
}