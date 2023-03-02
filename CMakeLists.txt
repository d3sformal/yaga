cmake_minimum_required(VERSION 3.17)

project(perun CXX)

include(FetchContent)

find_package(Catch2 3 QUIET)

if(FOUND_CATCH)
    message(STATUS "Using system install of Catch2")
else()
    message(STATUS "Fetching Catch2")

    FetchContent_Declare(
        Catch2
        GIT_REPOSITORY https://github.com/catchorg/Catch2.git
        GIT_TAG        v3.2.1
    )

    FetchContent_MakeAvailable(Catch2)

    message(STATUS "Fetching Catch2 - done")
endif()

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
    add_compile_options(-fdiagnostics-color=always)
    add_compile_options(-Wall -Wextra -Wpedantic)
elseif("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
    add_compile_options(-fcolor-diagnostics)
    add_compile_options(-Wall -Wextra -Wpedantic)
endif()

set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)

add_library(perun)
add_executable(test)
add_executable(sat src/sat_solver.cpp)
add_executable(smt src/smt_solver.cpp)

add_subdirectory(src)
add_subdirectory(tests)

target_compile_features(perun PRIVATE cxx_std_20)
target_compile_features(test PRIVATE cxx_std_20)
target_compile_features(sat PRIVATE cxx_std_20)
target_compile_features(smt PRIVATE cxx_std_20)

target_link_libraries(test PRIVATE perun Catch2::Catch2WithMain)
target_link_libraries(sat PRIVATE perun)
target_link_libraries(smt PRIVATE perun)