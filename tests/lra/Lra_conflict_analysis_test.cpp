#include <catch2/catch_test_macros.hpp>

#include "Lra_conflict_analysis.h"
#include "Linear_arithmetic.h"
#include "test.h"

TEST_CASE("FM elimination", "[fm]")
{
    using namespace perun;
    using namespace perun::test;

    using Rational = Fraction<int>;

    constexpr int num_reals = 5;

    Trail trail;
    trail.set_model<bool>(Variable::boolean, 0);
    trail.set_model<Rational>(Variable::rational, num_reals);
    Linear_arithmetic lra;
    lra.on_variable_resize(Variable::rational, num_reals);
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
            Fourier_motzkin_elimination fm{&lra, lb};
            Fourier_motzkin_elimination fm_ub{&lra, ub};
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
            Fourier_motzkin_elimination fm{&lra, lb};
            Fourier_motzkin_elimination fm_ub{&lra, ub};
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
            Fourier_motzkin_elimination fm{&lra, lb};
            Fourier_motzkin_elimination fm_ub{&lra, ub};
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
            Fourier_motzkin_elimination fm{&lra, lb};
            Fourier_motzkin_elimination fm_ub{&lra, ub};
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
            Fourier_motzkin_elimination fm{&lra, lb};
            Fourier_motzkin_elimination fm_ub{&lra, ub};
            fm.resolve(fm_ub, x.ord());

            auto derived = fm.finish(trail);
            REQUIRE(derived.lit() == make(4 * y - 9 * z == -13).lit());

            std::swap(lb, ub);
        }
    }
}