#include <catch2/catch_test_macros.hpp>

#include <array>

#include "Bounds.h"
#include "test.h"

TEST_CASE("Deduce a bound", "[bounds]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::literals;

    constexpr int num_vars = 5;

    Model<bool> bool_model;
    Model<Rational> lra_model;
    bool_model.resize(10);
    lra_model.resize(num_vars);
    Theory_models<Rational> models{bool_model, lra_model};
    Linear_constraints<Rational> repository;
    Bounds bounds;
    bounds.resize(num_vars);
    auto make = factory(repository);
    auto [x, y, z, w, a] = real_vars<num_vars>();

    SECTION("using elimination of bounded variables")
    {
        std::array constraints{
            make(2 * y + w > 2),
            make(3 * z + a <= 1),
            make(x + 3 * y - 2 * z <= 3),
        };
        for (auto cons : constraints)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }
        models.owned().set_value(w.ord(), 1);
        models.owned().set_value(a.ord(), 2);

        bounds.update(models, constraints[0]);
        bounds.update(models, constraints[1]);

        // add x upper bound by eliminating y and z
        bounds.deduce(models, constraints[2]);
        REQUIRE(bounds[x.ord()].upper_bound(models));
        REQUIRE(bounds[x.ord()].upper_bound(models)->value() == 5_r / 6);
        REQUIRE(bounds[x.ord()].upper_bound(models)->reason().lit() == constraints[2].lit());
        REQUIRE(bounds[x.ord()].upper_bound(models)->is_strict());
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds().size() == 2);
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds()[0].reason().lit() == constraints[0].lit());
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds()[1].reason().lit() == constraints[1].lit());
    }

    SECTION("using elimination of bounded variables with common variables")
    {
        std::array constraints{
            make(5 * z + 2 * a - 2 * w >= 2),
            make(2 * y - 3 * z + 3 * w >= 3),
            make(x + 2 * y + 3 * z + w + a <= 2),
        };
        for (auto cons : constraints)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }
        models.owned().set_value(w.ord(), 1);
        models.owned().set_value(a.ord(), 2);

        // add lower bound of z
        bounds.update(models, constraints[0]);

        // deduce lower bound of y
        bounds.deduce(models, constraints[1]);
        REQUIRE(bounds[y.ord()].lower_bound(models));
        REQUIRE(bounds[y.ord()].lower_bound(models)->value() == 0);
        REQUIRE(!bounds[y.ord()].lower_bound(models)->is_strict());
        REQUIRE(bounds[y.ord()].lower_bound(models)->reason().lit() == constraints[1].lit());
        REQUIRE(bounds[y.ord()].lower_bound(models)->bounds().size() == 1);
        REQUIRE(bounds[y.ord()].lower_bound(models)->bounds()[0].reason().lit() == constraints[0].lit());

        // deduce upper bound of x from lower bound of y and z
        bounds.deduce(models, constraints[2]);
        REQUIRE(bounds[x.ord()].upper_bound(models));
        REQUIRE(bounds[x.ord()].upper_bound(models)->value() == -1);
        REQUIRE(bounds[x.ord()].upper_bound(models)->reason().lit() == constraints[2].lit());
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds().size() == 2);
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds()[0].reason().lit() == constraints[1].lit());
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds()[1].reason().lit() == constraints[0].lit());
    }

    SECTION("from an equality")
    {
        std::array constraints{
            make(y <= 2),
            make(y >= 1),
            make(z <= 3),
            make(z >= 1),
            make(2 * x - 3 * y + 5 * z == 1),
        };
        for (auto cons : constraints)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
        }
        bounds.update(models, constraints[0]);
        bounds.update(models, constraints[1]);
        bounds.update(models, constraints[2]);
        bounds.update(models, constraints[3]);

        bounds.deduce(models, constraints[4]);
        REQUIRE(bounds[x.ord()].upper_bound(models));
        REQUIRE(bounds[x.ord()].upper_bound(models)->value() == 1);
        REQUIRE(bounds[x.ord()].upper_bound(models)->reason().lit() == constraints[4].lit());
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds().size() == 2);
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds()[0].reason().lit() == constraints[0].lit());
        REQUIRE(bounds[x.ord()].upper_bound(models)->bounds()[1].reason().lit() == constraints[3].lit());

        REQUIRE(bounds[x.ord()].lower_bound(models));
        REQUIRE(bounds[x.ord()].lower_bound(models)->value() == -11_r / 2);
        REQUIRE(bounds[x.ord()].lower_bound(models)->reason().lit() == constraints[4].lit());
        REQUIRE(bounds[x.ord()].lower_bound(models)->bounds().size() == 2);
        REQUIRE(bounds[x.ord()].lower_bound(models)->bounds()[0].reason().lit() == constraints[1].lit());
        REQUIRE(bounds[x.ord()].lower_bound(models)->bounds()[1].reason().lit() == constraints[2].lit());
    }
}

TEST_CASE("Check if an unassigned constraint is implied by bounds", "[bounds]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::literals;

    constexpr int num_vars = 5;

    Model<bool> bool_model;
    Model<Rational> lra_model;
    bool_model.resize(10);
    lra_model.resize(num_vars);
    Theory_models<Rational> models{bool_model, lra_model};
    Linear_constraints<Rational> repository;
    Bounds bounds;
    bounds.resize(num_vars);
    auto make = factory(repository);
    auto [x, y, z, w, a] = real_vars<num_vars>();

    SECTION("Detect implied constraints")
    {
        std::array constraints{
            make(x <= 3),
            make(y >= 1),
            make(z <= 2),
        };
        for (auto cons : constraints)
        {
            models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
            bounds.update(models, cons);
        }

        REQUIRE(!bounds.is_implied(models, make(2 * x - 3 * y + 5 * z < 13)));
        REQUIRE(bounds.is_implied(models, make(2 * x - 3 * y + 5 * z <= 13)));
        REQUIRE(bounds.is_implied(models, make(2 * x - 3 * y + 5 * z <= 14)));
    }
}