#ifndef PERUN_SMT2_PARSER_H
#define PERUN_SMT2_PARSER_H

#include <string>

namespace perun::parser {

class Smt2_parser {
public:
    void parse_file(std::string const& file_name);
};

} // namespace perun::parser

#endif // PERUN_SMT2_PARSER_H
