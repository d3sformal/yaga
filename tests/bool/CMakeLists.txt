target_include_directories(test PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(test PRIVATE
    Bool_theory_test.cpp
)