#ifndef YAGA_SMT2_PARSER_H
#define YAGA_SMT2_PARSER_H

#include <string>
#include <istream>
#include <ostream>
#include <stdexcept>
#include <fstream>
#include <vector>

#include "Options.h"
#include "Smt2_term_parser.h"
#include "Term_manager.h"
#include "Term_types.h"
#include "smt2_lexer.h"
#include "Solver_wrapper.h"

namespace yaga::parser {

#define UNIMPLEMENTED throw std::logic_error("Not implemented yet!")

using term_t = terms::term_t;

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

    smt2_lexer lexer;

    terms::Term_manager term_manager;
    std::vector<term_t> assertions;
    std::optional<Solver_answer> last_answer;

    bool parse_command(std::ostream& output,
                       Smt2_term_parser& term_parser,
                       Parser_context& parser_context);

    void parse_error(std::string const& msg);

    static void print_answer(Solver_answer answer,  std::ostream& output);

    std::pair<std::vector<term_t>, std::vector<term_t>> assign_terms_by_name_to_groups(const std::unordered_set<std::string>& group1, const std::unordered_set<std::string>& group2);
};

} // namespace yaga::parser

#endif // YAGA_SMT2_PARSER_H
