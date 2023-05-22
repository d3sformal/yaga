target_include_directories(yaga PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(yaga PRIVATE
    Bounds.cpp
    Linear_arithmetic.cpp
    Lra_conflict_analysis.cpp
    Long_fraction.cpp
)