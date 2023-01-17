target_include_directories(test PUBLIC ${CMAKE_CURRENT_LIST_DIR})

add_subdirectory(bool)
add_subdirectory(lra)

target_sources(test PRIVATE
    Conflict_analysis_test.cpp
    Evsids_test.cpp
    Glucose_restart_test.cpp
    Luby_restart_test.cpp
    Solver_test.cpp
    Subsumption_test.cpp
)