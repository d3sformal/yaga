#include <catch2/catch_test_macros.hpp>

#include <array>

#include "Restart.h"

TEST_CASE("Generate luby sequence", "[luby]")
{
    using namespace perun;

    std::array seq{
        0, 
        1, 1, 2, 
        1, 1, 2, 4,
        1, 1, 2, 
        1, 1, 2, 4, 8,
        1, 1, 2, 
        1, 1, 2, 4,
        1, 1, 2, 
        1, 1, 2, 4, 8, 16,
    };

    Luby_restart restart;
    for (std::size_t i = 1; i < seq.size(); ++i)
    {
        REQUIRE(restart.luby(i) == seq[i]);
    }
}