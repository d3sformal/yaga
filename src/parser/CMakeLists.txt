find_package(FLEX 2.6.4 REQUIRED)

FLEX_TARGET(smt2_lexer smt2_lexer.ll ${CMAKE_CURRENT_BINARY_DIR}/smt2_lexer.cpp)

add_library(yaga_lexer OBJECT ${FLEX_smt2_lexer_OUTPUTS})

target_include_directories(yaga_lexer PUBLIC ${CMAKE_CURRENT_LIST_DIR})

target_link_libraries(yaga PUBLIC yaga_lexer)

target_sources(yaga PRIVATE
        Flex_lexer.cpp
        Smt2_parser.cpp
        Smt2_term_parser.cpp
        Parser_context.cpp
        Solver_wrapper.cpp
        )


#add_executable(lexer_test lexer_test.cpp Flex_lexer.cpp ${FLEX_smt2_lexer_OUTPUTS})

#target_compile_features(lexer_test PRIVATE cxx_std_20)
#target_include_directories(lexer_test PUBLIC ${CMAKE_CURRENT_LIST_DIR})
#if (FLEX_INCLUDE_DIRS)
#    target_include_directories(lexer_test PUBLIC ${FLEX_INCLUDE_DIRS})
#endif(FLEX_INCLUDE_DIRS)
