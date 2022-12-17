#include <iostream>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <chrono>

#include "Solver.h"
#include "Evsids.h"
#include "Restart.h"
#include "Bool_theory.h"

using namespace perun;

bool is_satisfying(const Trail& trail, const Database& db)
{
    const auto& model = trail.model<bool>(Variable::boolean);
    return std::all_of(db.asserted().begin(), db.asserted().end(), [&](const auto& clause) {
        return std::any_of(clause.begin(), clause.end(), [&](auto lit) {
            return model.is_defined(lit.var().ord()) && model.value(lit.var().ord()) == !lit.is_negation();
        });
    });
}

int main(int argc, char** argv)
{
    if (argc != 2)
    {
        std::cerr << "Usage: ./sat [input-path.cnf]" << std::endl;
        return -1;
    }

    Solver solver;
    solver.set_theory<Bool_theory>();
    solver.set_variable_order<Evsids>();
    solver.set_restart_policy<Luby_restart>();

    std::string path{argv[1]};
    std::ifstream input{path};
    int num_vars = 0;
    int num_clauses = 0;
    Clause buffer;
    for (;;)
    {
        std::string line;
        std::getline(input, line);
        if (input.fail() || input.eof())
        {
            break;
        }

        std::stringstream stream{line};
        if (line.starts_with('c'))
        {
            continue;
        }
        else if (line.starts_with("p cnf"))
        {
            stream.seekg(5);
            stream >> num_vars >> num_clauses;
            solver.trail().set_model<bool>(Variable::boolean, num_vars);
        }
        else
        {
            for (;;)
            {
                int var;
                stream >> var;
                if (stream.fail())
                {
                    break;
                }

                if (!buffer.empty() && var == 0)
                {
                    solver.db().assert_clause(std::move(buffer));
                    buffer.clear();
                    --num_clauses;
                }
                else if (num_clauses > 0)
                {
                    buffer.emplace_back(var < 0 ? Literal{-var - 1}.negate() : Literal{var - 1});
                }
            }
        }
    }

    auto begin = std::chrono::steady_clock::now();
    auto result = solver.check();
    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin);
    if (result == Solver::sat)
    {
        if (is_satisfying(solver.trail(), solver.db()))
        {
            std::cout << "SAT\n";
        }
        else
        {
            std::cout << "ERROR\n";
            return -2;
        }
    }
    else 
    {
        std::cout << "UNSAT\n";
    }

    std::cout << "\n";
    std::cout << "time[s] = " << (duration.count() / 1e9) << "\n";
    std::cout << "conflicts = " << solver.num_conflicts() << "\n";
    std::cout << "decisions = " << solver.num_decisions() << "\n";
    std::cout << "restarts = " << solver.num_restarts() << "\n";

    return result == Solver::sat ? 1 : 0;
}