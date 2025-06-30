#ifndef YAGA_UTILS_H
#define YAGA_UTILS_H

#include <iostream>

#include "Term_manager.h"

namespace yaga::utils
{

class Utils
{
public:
    static void print_term(terms::term_t, terms::Term_manager const& term_manager, int tabs = 0, std::string const& endline = "\n");
    static void pretty_print_term(terms::term_t t, const terms::Term_manager& tm, std::ostream& out);
};

} // namespace yaga::utils

#endif // YAGA_UTILS_H
