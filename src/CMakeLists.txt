target_include_directories(yaga PUBLIC ${CMAKE_CURRENT_LIST_DIR})

add_subdirectory(bool)
add_subdirectory(lra)
add_subdirectory(variable_order)
add_subdirectory(terms)
add_subdirectory(parser)

target_sources(yaga PRIVATE
    Conflict_analysis.cpp
    Yaga.cpp
    Solver.cpp
    Subsumption.cpp
    Trail.cpp
    Theory.cpp
    Theory_combination.cpp
)