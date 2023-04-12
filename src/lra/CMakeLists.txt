target_include_directories(perun PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(perun PRIVATE
    Linear_arithmetic.cpp
    Lra_conflict_analysis.cpp
    Long_fraction.cpp
)