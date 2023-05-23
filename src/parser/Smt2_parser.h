#ifndef YAGA_SMT2_PARSER_H
#define YAGA_SMT2_PARSER_H

#include <string>
#include <istream>
#include <ostream>

namespace yaga::parser {

class Smt2_parser {
public:
    void parse_file(std::string const& file_name);

    void parse(std::istream& input, std::ostream& output);
};

} // namespace yaga::parser

#endif // YAGA_SMT2_PARSER_H
