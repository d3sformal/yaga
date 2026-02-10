target_include_directories(test PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_sources(test PRIVATE
        Interpolation_test.cpp
        Interpolation_parsing_test.cpp
        Check_modulo_model_test.cpp
)