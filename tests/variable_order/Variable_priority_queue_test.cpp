#include <catch2/catch_test_macros.hpp>

#include <limits>

#include "Variable_priority_queue.h"

TEST_CASE("Insert variables to the priority queue", "[variable_priority_queue]")
{
    using namespace yaga;

    Variable_priority_queue pq;
    REQUIRE(pq.empty());

    SECTION("in ascending order")
    {
        pq.push(Variable{1, Variable::boolean}, 1.f);
        pq.push(Variable{2, Variable::boolean}, 2.f);
        pq.push(Variable{3, Variable::rational}, 3.f);
        pq.push(Variable{4, Variable::rational}, 4.f);

        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{4, Variable::rational});
        
        pq.pop();
        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{3, Variable::rational});

        pq.pop();
        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{2, Variable::boolean});

        pq.pop();
        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{1, Variable::boolean});

        REQUIRE(!pq.empty());
    }

    SECTION("in descending order")
    {
        pq.push(Variable{4, Variable::rational}, 4.f);
        pq.push(Variable{3, Variable::rational}, 3.f);
        pq.push(Variable{2, Variable::boolean}, 2.f);
        pq.push(Variable{1, Variable::boolean}, 1.f);

        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{4, Variable::rational});
        
        pq.pop();
        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{3, Variable::rational});

        pq.pop();
        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{2, Variable::boolean});

        pq.pop();
        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{1, Variable::boolean});

        REQUIRE(!pq.empty());
    }
}

TEST_CASE("Increase score of variables in the priority queue", "[variable_priority_queue]")
{
    using namespace yaga;

    Variable_priority_queue pq;
    REQUIRE(pq.empty());

    pq.push(Variable{1, Variable::boolean}, 1.f);
    pq.push(Variable{2, Variable::boolean}, 1.f);
    pq.push(Variable{3, Variable::rational}, 1.f);
    pq.push(Variable{4, Variable::rational}, 1.f);

    REQUIRE(!pq.empty());

    pq.update(Variable{3, Variable::rational}, 2.f);
    REQUIRE(!pq.empty());
    REQUIRE(pq.top() == Variable{3, Variable::rational});
    
    pq.pop();
    pq.update(Variable{2, Variable::boolean}, 2.f);
    REQUIRE(!pq.empty());
    REQUIRE(pq.top() == Variable{2, Variable::boolean});

    pq.pop();
    pq.update(Variable{4, Variable::rational}, 2.f);
    REQUIRE(!pq.empty());
    REQUIRE(pq.top() == Variable{4, Variable::rational});

    pq.pop();
    REQUIRE(!pq.empty());
    REQUIRE(pq.top() == Variable{1, Variable::boolean});

    pq.pop();
    REQUIRE(pq.empty());
}

TEST_CASE("Replace a range of values", "[variable_priority_queue]")
{
    using namespace yaga;

    Variable_priority_queue pq;
    REQUIRE(pq.empty());

    pq.push(Variable{1, Variable::boolean}, 1);
    pq.push(Variable{2, Variable::boolean}, 2);
    pq.push(Variable{3, Variable::boolean}, 3);
    pq.push(Variable{4, Variable::boolean}, 4);

    pq.pop();
    pq.pop();
    pq.pop();
    pq.pop();
    REQUIRE(pq.empty());

    pq.push(Variable{1, Variable::boolean}, 4);
    pq.push(Variable{2, Variable::boolean}, 3);
    pq.push(Variable{3, Variable::boolean}, 2);
    pq.push(Variable{4, Variable::boolean}, 1);

    REQUIRE(pq.top() == Variable{1, Variable::boolean});

    pq.pop();
    REQUIRE(pq.top() == Variable{2, Variable::boolean});

    pq.pop();
    REQUIRE(pq.top() == Variable{3, Variable::boolean});

    pq.pop();
    REQUIRE(pq.top() == Variable{4, Variable::boolean});

    pq.pop();
    REQUIRE(pq.empty());
}

TEST_CASE("Add a large number of variables to the queue", "[variable_priority_queue]")
{
    using namespace yaga;

    Variable_priority_queue pq;
    REQUIRE(pq.empty());

    int constexpr num_vars = 20;

    for (int i = 0; i < num_vars; ++i)
    {
        pq.push(Variable{i, Variable::boolean}, i);
    }

    for (int i = num_vars - 1; i >= 0; --i)
    {
        REQUIRE(!pq.empty());
        REQUIRE(pq.top() == Variable{i, Variable::boolean});
        pq.pop();
    }
    REQUIRE(pq.empty());
}

TEST_CASE("Reorder variables after rescale resets scores to 0", "[variable_priority_queue]")
{
    using namespace yaga;

    Variable_priority_queue pq;
    REQUIRE(pq.empty());

    int constexpr num_vars = 50;
    for (int i = 0; i < num_vars; ++i)
    {
        pq.push(Variable{i, Variable::boolean}, i / 1e10f);
    }

    pq.rescale(std::numeric_limits<float>::max());

    for (int i = 0; i < num_vars; ++i)
    {
        REQUIRE(pq.top() == Variable{i, Variable::boolean});
        pq.pop();
    }
}