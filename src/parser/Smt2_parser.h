#ifndef YAGA_SMT2_PARSER_H
#define YAGA_SMT2_PARSER_H

#include <string>

namespace yaga::parser {

class Smt2_parser {
public:
    void parse_file(std::string const& file_name);
};

} // namespace yaga::parser

#endif // YAGA_SMT2_PARSER_H
