#ifndef YAGA_SMT2_PARSER_H
#define YAGA_SMT2_PARSER_H

#include <string>
#include <istream>
#include <ostream>

#include "Options.h"

namespace yaga::parser {

class Smt2_parser {
public:
    void parse_file(std::string const& file_name);

    void parse(std::istream& input, std::ostream& output);

    /** Set new options
     * 
     * @param opts new solver options
     */
    inline void set_options(Options const& opts) { options = opts; }
private:
    // parsed command line options for the solver
    Options options;
};

} // namespace yaga::parser

#endif // YAGA_SMT2_PARSER_H
