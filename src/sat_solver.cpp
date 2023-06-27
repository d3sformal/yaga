#include <algorithm>
#include <chrono>
#include <cctype>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "Bool_theory.h"
#include "Evsids.h"
#include "Restart.h"
#include "Solver.h"

using namespace yaga;

bool is_satisfying(Trail const& trail, Database const& db)
{
    auto const& model = trail.model<bool>(Variable::boolean);
    return std::all_of(db.asserted().begin(), db.asserted().end(), [&](auto const& clause) {
        return std::any_of(clause.begin(), clause.end(), [&](auto lit) {
            return model.is_defined(lit.var().ord()) &&
                   model.value(lit.var().ord()) == !lit.is_negation();
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
    solver.set_restart_policy<Glucose_restart>();

    std::string path{argv[1]};
    std::ifstream input{path};
    bool is_initialized = false;
    int num_vars = 0;
    int num_clauses = 0;
    Clause buffer;
    std::string line;
    while (std::getline(input, line))
    {
        line.erase(line.begin(), std::find_if(line.begin(), line.end(), [](auto c) {
            return !std::isspace(c);
        }));

        std::istringstream stream{line};
        if (line.starts_with('c'))
        {
            continue;
        }
        else if (line.starts_with("p cnf"))
        {
            if (is_initialized)
            {
                std::cerr << "Error: duplicate DIMACS problem line 'p cnf ...'\n";
                return -1;
            }
            is_initialized = true;
            stream.seekg(5);
            if (!(stream >> num_vars >> num_clauses))
            {
                std::cerr << "Error: failed to parse the DIMACS problem line." 
                    << " Expected: 'p cnf [num_vars] [num_clauses]'\n";
                return -1;
            }
            solver.trail().set_model<bool>(Variable::boolean, num_vars);
        }
        else
        {
            int var;
            while (stream >> var)
            {
                if (!is_initialized)
                {
                    std::cerr << "Error: clause before DIMACS problem line.\n";
                    return -1;
                }
                else if (var > num_vars || var < -num_vars)
                {
                    std::cerr << "Error: unkown literal " << var << "\n";
                    return -1;
                }

                if (var == 0)
                {
                    if (num_clauses > 0 && buffer.empty())
                    {
                        std::cout << "UNSAT\n";
                        return 0;
                    }

                    if (num_clauses > 0)
                    {
                        solver.db().assert_clause(std::move(buffer));
                    }
                    buffer.clear();
                    --num_clauses;
                }
                else
                {
                    buffer.emplace_back(var < 0 ? ~Literal{-var - 1} : Literal{var - 1});
                }
            }
        }
    }

    if (!is_initialized)
    {
        std::cerr << "Error: missing DIMANCS problem line. " 
            << "Expected 'p cnf [num_vars] [num_clauses]'\n";
        return -1;
    }

    if (num_clauses > 0)
    {
        std::cerr << "Error: insufficient number of clauses.\n";
        return -1;
    }

    auto begin = std::chrono::steady_clock::now();
    auto result = solver.check();
    auto end = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin);
    if (result == Solver::Result::sat)
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

    return result == Solver::Result::sat ? 1 : 0;
}