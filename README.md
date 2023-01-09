# Perun

MCSat SMT solver developed at MFF UK, mainly by M. Blicha, D. Hanák, and J. Kofroň (in alphabetic order).

## Build

You will need a C++ compiler (`gcc`, `clang`) with C++20 support and `cmake` version at least 3.17. Run the following commands to build the project:

1. `mkdir build-release`
2. `cd build-release`
3. `cmake -DCMAKE_BUILD_TYPE=Release ..`
4. `make` 

You can use a different build system in step `3`. For example, `cmake -DCMAKE_BUILD_TYPE=Release -G Ninja ..` creates build files for the [Ninja build system](https://ninja-build.org/) which you can use in the 4th step by running `ninja` instead of `make`.

Building the project creates `test` and `sat` executables. The `sat` utility implements a SAT solver using core of the MCSat framework and a plugin for boolean variables. It has one command line argument which is a path to a CNF formula in the [DIMACS format](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/SATLINK____DIMACS).