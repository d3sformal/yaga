#include <catch2/catch_test_macros.hpp>

#include "Rational.h"

TEST_CASE("Arithmetic operations with fractions", "[fraction]")
{
    using namespace yaga;
    using namespace yaga::literals;

    SECTION("Compare fractions")
    {
        REQUIRE(2_r / 6 == 1_r / 3);
        REQUIRE(3_r == 3);
        REQUIRE(1_r / -6 == -1_r / 6);
        REQUIRE(-1_r / -6 == 1_r / 6);
        REQUIRE(0_r == 0_r / 6);
        REQUIRE(0_r == 0_r / 5);
        REQUIRE(0_r / 3 == 0_r / 5);
    }

    SECTION("Add fractions")
    {
        REQUIRE(1_r / 4 + 1_r / 6 == 5_r / 12);
        REQUIRE(1_r / 4 + 2 == 9_r / 4);
        REQUIRE(2_r + 1_r / 4 == 9_r / 4);
        REQUIRE(1_r / 1073741824 + 1_r / 2 == 536870913_r / 1073741824);
    }

    SECTION("Subtract fractions")
    {
        REQUIRE(1_r / 4 - 1_r / 6 == 1_r / 12);
        REQUIRE(1_r / 4 - 2 == -7_r / 4);
        REQUIRE(2_r - 1_r / 4 == 7_r / 4);
        REQUIRE(1_r / 1073741824 - 1_r / 2 == -536870911_r / 1073741824);
    }

    SECTION("Multiply fractions")
    {
        REQUIRE((3_r / 4) * (1_r / 6) == 1_r / 8);
        REQUIRE((3_r / 4) * 2 == 3_r / 2);
        REQUIRE(2_r * (3_r / 4) == 3_r / 2);
    }

    SECTION("Divide fractions")
    {
        REQUIRE((3_r / 4) / (5_r / 6) == 9_r / 10);
        REQUIRE((3_r / 4) / 2 == 3_r / 8);
        REQUIRE(2_r / (3_r / 4) == 8_r / 3);
    }

    SECTION("normalize inverse")
    {
        REQUIRE((-1_r / 2).inv().numerator() == -2);
        REQUIRE((-1_r / 2).inv().denominator() == 1);
        REQUIRE((1_r / -2).inv().numerator() == -2);
        REQUIRE((1_r / -2).inv().denominator() == 1);
    }
}

TEST_CASE("Compare fractions", "[fraction]")
{
    using namespace yaga;
    using namespace yaga::literals;

    SECTION("with maximal int value")
    {
        REQUIRE(1_r / 2 < std::numeric_limits<int>::max());
        REQUIRE(1_r / 2 <= std::numeric_limits<int>::max());
        REQUIRE(1_r / 2 < Rational{std::numeric_limits<int>::max()});
        REQUIRE(1_r / 2 <= Rational{std::numeric_limits<int>::max()});
        REQUIRE(Rational{std::numeric_limits<int>::lowest()} <= Rational{std::numeric_limits<int>::max()});
        REQUIRE(Rational{std::numeric_limits<int>::lowest()} < Rational{std::numeric_limits<int>::max()});
    }

    SECTION("with minimal int value")
    {
        REQUIRE(1_r / 2 > std::numeric_limits<int>::lowest());
        REQUIRE(1_r / 2 >= std::numeric_limits<int>::lowest());
        REQUIRE(1_r / 2 > Rational{std::numeric_limits<int>::lowest()});
        REQUIRE(1_r / 2 >= Rational{std::numeric_limits<int>::lowest()});
    }
}