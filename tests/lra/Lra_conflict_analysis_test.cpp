#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_vector.hpp>

#include "Lra_conflict_analysis.h"
#include "Linear_arithmetic.h"
#include "test.h"
#include "Rational.h"

TEST_CASE("FM elimination", "[fm]")
{
    using namespace yaga;
    using namespace yaga::test;

    constexpr int num_reals = 5;

    Linear_arithmetic lra;
    Event_dispatcher dispatcher;
    dispatcher.add(&lra);
    Trail trail{dispatcher};
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, num_reals);
    auto [x, y, z, w, a] = real_vars<num_reals>();
    auto make = factory(lra, trail);
    auto models = lra.relevant_models(trail);

    SECTION("non-strict inequalities")
    {
        auto lb = make(3 * x + 2 * y <= 1);
        auto ub = make(2 * x + 3 * z >= 5);
        models.owned().set_value(y.ord(), 0);
        trail.propagate(y, nullptr, 0);
        models.owned().set_value(z.ord(), 0);
        trail.propagate(z, nullptr, 0);

        for (int i = 0; i < 2; ++i)
        {
            Fm_elimination fm{&lra, lb};
            Fm_elimination fm_ub{&lra, ub};
            fm.resolve(fm_ub, x.ord());

            auto derived = fm.finish(trail);
            REQUIRE(derived.lit() == make(4 * y - 9 * z <= -13).lit());

            std::swap(lb, ub);
        }
    }

    SECTION("with one strict inequality")
    {
        auto lb = make(3 * x + 2 * y < 1);
        auto ub = make(2 * x + 3 * z >= 5);
        models.owned().set_value(y.ord(), 0);
        trail.propagate(y, nullptr, 0);
        models.owned().set_value(z.ord(), 0);
        trail.propagate(z, nullptr, 0);

        for (int i = 0; i < 2; ++i)
        {
            Fm_elimination fm{&lra, lb};
            Fm_elimination fm_ub{&lra, ub};
            fm.resolve(fm_ub, x.ord());

            auto derived = fm.finish(trail);
            REQUIRE(derived.lit() == make(4 * y - 9 * z < -13).lit());

            std::swap(lb, ub);
        }
    }

    SECTION("with one equality as a lower bound")
    {
        auto lb = make(3 * x + 2 * y <= 1);
        auto ub = make(2 * x + 3 * z == 5);
        models.owned().set_value(y.ord(), 0);
        trail.propagate(y, nullptr, 0);
        models.owned().set_value(z.ord(), 0);
        trail.propagate(z, nullptr, 0);

        for (int i = 0; i < 2; ++i)
        {
            Fm_elimination fm{&lra, lb};
            Fm_elimination fm_ub{&lra, ub};
            fm.resolve(fm_ub, x.ord());

            auto derived = fm.finish(trail);
            REQUIRE(derived.lit() == make(4 * y - 9 * z <= -13).lit());

            std::swap(lb, ub);
        }
    }

    SECTION("with one equality as an upper bound")
    {
        auto lb = make(3 * x + 2 * y >= 1);
        auto ub = make(2 * x + 3 * z == 5);
        models.owned().set_value(y.ord(), 0);
        trail.propagate(y, nullptr, 0);
        models.owned().set_value(z.ord(), 0);
        trail.propagate(z, nullptr, 0);

        for (int i = 0; i < 2; ++i)
        {
            Fm_elimination fm{&lra, lb};
            Fm_elimination fm_ub{&lra, ub};
            fm.resolve(fm_ub, x.ord());

            auto derived = fm.finish(trail);
            REQUIRE(derived.lit() == make(-4 * y + 9 * z <= 13).lit());

            std::swap(lb, ub);
        }
    }

    SECTION("with two equalities")
    {
        auto lb = make(3 * x + 2 * y == 1);
        auto ub = make(2 * x + 3 * z == 5);
        models.owned().set_value(y.ord(), 0);
        trail.propagate(y, nullptr, 0);
        models.owned().set_value(z.ord(), 0);
        trail.propagate(z, nullptr, 0);

        for (int i = 0; i < 2; ++i)
        {
            Fm_elimination fm{&lra, lb};
            Fm_elimination fm_ub{&lra, ub};
            fm.resolve(fm_ub, x.ord());

            auto derived = fm.finish(trail);
            REQUIRE(derived.lit() == make(4 * y - 9 * z == -13).lit());

            std::swap(lb, ub);
        }
    }
}

TEST_CASE("Derive bound conflict when some variables are not assigned", "[bound_conflict]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::literals;

    constexpr int num_reals = 5;

    Linear_arithmetic lra;
    Event_dispatcher dispatcher;
    dispatcher.add(&lra);
    Trail trail{dispatcher};
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, num_reals);

    Bounds bounds;
    bounds.resize(num_reals);
    auto [x, y, z, a, b] = real_vars<num_reals>();
    auto make = factory(lra, trail);
    auto models = lra.relevant_models(trail);

    std::array constraints{
        make(z <= 1),
        make(y + 2 * z + a >= 0),
        make(x + 2 * y + 3 * a <= 4),
        make(x + 4 * z + 2 * b > 0),
    };
    for (auto cons : constraints)
    {
        models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
    }
    trail.propagate(a, nullptr, 0);
    models.owned().set_value(a.ord(), 16);
    trail.propagate(b, nullptr, 0);
    models.owned().set_value(b.ord(), 2);

    // add all bounds
    bounds[z.ord()].add_upper_bound(models, {z.ord(), 1, constraints[0], models});
    REQUIRE(bounds[z.ord()].upper_bound(models));

    bounds[y.ord()].add_lower_bound(models, {y.ord(), -18, constraints[1], models, 
        std::vector{*bounds[z.ord()].upper_bound(models)}});
    REQUIRE(bounds[y.ord()].lower_bound(models));

    bounds[x.ord()].add_upper_bound(models, {x.ord(), -8, constraints[2], models,
        std::vector{*bounds[y.ord()].lower_bound(models)}});
    REQUIRE(bounds[z.ord()].upper_bound(models));

    bounds[x.ord()].add_lower_bound(models, {x.ord(), -8, constraints[3], models,
        std::vector{*bounds[z.ord()].upper_bound(models)}});
    REQUIRE(bounds[x.ord()].lower_bound(models));
    
    Bound_conflict_analysis analysis{&lra};
    auto conflict = analysis.analyze(trail, bounds, x.ord());
    REQUIRE(conflict);
    REQUIRE_THAT(*conflict, Catch::Matchers::UnorderedEquals(clause(
        ~constraints[0],
        ~constraints[1],
        ~constraints[2],
        ~constraints[3],
        make(a - 2 * b < 12)
    )));
}

TEST_CASE("Derive inequality conflict when some variables are not assigned", "[inequality_conflict]")
{
    using namespace yaga;
    using namespace yaga::test;
    using namespace yaga::literals;

    constexpr int num_reals = 7;

    Linear_arithmetic lra;
    Event_dispatcher dispatcher;
    dispatcher.add(&lra);
    Trail trail{dispatcher};
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, num_reals);
    Bounds bounds;
    bounds.resize(num_reals);
    auto [x, y, z, w, a, b, c] = real_vars<num_reals>();
    auto make = factory(lra, trail);
    auto models = lra.relevant_models(trail);

    std::array constraints{
        make(z >= 2),
        make(y + 2 * z <= 1),
        make(x + 2 * y + 3 * a >= 0),
        make(x + 5 * z + 2 * b <= 0),
        make(x + 3 * c != -3),
    };
    for (auto cons : constraints)
    {
        models.boolean().set_value(cons.lit().var().ord(), !cons.lit().is_negation());
    }
    models.owned().set_value(a.ord(), 2);
    models.owned().set_value(b.ord(), -5);
    models.owned().set_value(c.ord(), -1);
    trail.propagate(a, nullptr, 0);
    trail.propagate(b, nullptr, 0);
    trail.propagate(c, nullptr, 0);

    // add all bounds
    bounds[z.ord()].add_lower_bound(models, {z.ord(), 2, constraints[0], models});
    REQUIRE(bounds[z.ord()].lower_bound(models));

    bounds[y.ord()].add_upper_bound(models, {y.ord(), -3, constraints[1], models,
        std::vector{*bounds[z.ord()].lower_bound(models)}});
    REQUIRE(bounds[y.ord()].upper_bound(models));

    bounds[x.ord()].add_lower_bound(models, {x.ord(), 0, constraints[2], models,
        std::vector{*bounds[y.ord()].upper_bound(models)}});
    REQUIRE(bounds[x.ord()].lower_bound(models));

    bounds[x.ord()].add_upper_bound(models, {x.ord(), 0, constraints[3], models,
        std::vector{*bounds[z.ord()].lower_bound(models)}});
    REQUIRE(bounds[x.ord()].upper_bound(models));

    bounds[x.ord()].add_inequality(models, {x.ord(), 0, constraints[4], models});
    REQUIRE(bounds[x.ord()].inequality(models, 0));

    Inequality_conflict_analysis analysis{&lra};
    auto conflict = analysis.analyze(trail, bounds, x.ord());
    REQUIRE(conflict);
    REQUIRE_THAT(*conflict, Catch::Matchers::UnorderedEquals(clause(
        ~constraints[0],
        ~constraints[1],
        ~constraints[2],
        ~constraints[3],
        ~constraints[4],
        make(c - a < -3),
        make(2 * b - 3 * c < -7)
    )));
}