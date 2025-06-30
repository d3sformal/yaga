#include "Utils.h"

namespace yaga::utils {

void Utils::print_term(terms::term_t t, const terms::Term_manager& term_manager, int tabs, std::string const& endline) {
    bool args = false;
    bool type = false;

    for (int i = 0; i < tabs; ++i)
    {
        std::cout << "\t";
    }

    std::cout << "(" << t.x << "): ";

    if (term_manager.is_negated(t))
        std::cout << "negation of ";

    t = term_manager.positive_term(t);
    auto kind = term_manager.get_kind(t);

    switch (kind)
    {
    case terms::Kind::UNINTERPRETED_TERM:
        //std::cout << "UNINTERPRETED_TERM: ";
        if (term_manager.get_term_name(t).has_value())
            std::cout << term_manager.get_term_name(t).value();
        type = true;
        break;
    case terms::Kind::ARITH_BINEQ_ATOM:
        std::cout << "ARITH_BINEQ_ATOM";
        args = true;
        break;
    case terms::Kind::ARITH_CONSTANT:
        //std::cout << "ARITH_CONSTANT: ";
        std::cout << term_manager.arithmetic_constant_value(t);
        break;
    case terms::Kind::ARITH_PRODUCT:
        std::cout << "ARITH_PRODUCT";/*
        print_term(term_manager.get_args(t)[0], term_manager);
        std::cout << " * ";
        print_term(term_manager.get_args(t)[1], term_manager);*/
        args = true;
        break;
    case terms::Kind::ARITH_EQ_ATOM:
        std::cout << "ARITH_EQ_ATOM";
        args = true;
        break;
    case terms::Kind::ARITH_GE_ATOM:
        std::cout << "ARITH_GE_ATOM";
        args = true;
        break;
    case terms::Kind::ARITH_POLY:
        std::cout << "ARITH_POLY";
        args = true;
        break;
    case terms::Kind::CONSTANT_TERM:
        std::cout << "CONSTANT_TERM";
        type = true;
        break;
    case terms::Kind::OR_TERM:
        std::cout << "OR_TERM";
        args = true;
        break;
    case terms::Kind::XOR_TERM:
        std::cout << "XOR_TERM";
        args = true;
        break;
    case terms::Kind::APP_TERM:
        std::cout << "FUNCTION " << term_manager.get_term_name(term_manager.get_fnc_symbol(t)).value();
        args = true; type = true;
        break;
    default:
        printf("other");
        break;
    }

    if (type) {
        std::string type_alias;
        auto type_num = term_manager.get_type(t);
        if (type_num == 0) {
            type_alias = "Bool";
        } else if (type_num == 1) {
            type_alias = "Real";
        }
        std::cout << " (" << type_alias << ")";
    }

    if (args) {
        int new_tabs = tabs+1;
        auto t_args = term_manager.get_args(t);
        std::cout << ", args:" << std::endl;

        for (size_t i = 0; i < t_args.size(); ++i)
        {
            print_term(t_args[i], term_manager, new_tabs, endline);
        }
    } else {
        std::cout << endline;
    }
}

void Utils::pretty_print_term(terms::term_t t, const terms::Term_manager& tm, std::ostream& out) {
    if (tm.is_negated(t)) {
        t = tm.positive_term(t);
        out << "(not ";
        pretty_print_term(t, tm, out);
        out << ")";
        return;
    }

    auto kind = tm.get_kind(t);
    auto args = tm.get_args(t);

    switch (kind) {
    case terms::Kind::UNINTERPRETED_TERM:
        out << tm.get_term_name(t).value_or("<?>");
        break;

    case terms::Kind::CONSTANT_TERM:
    case terms::Kind::ARITH_CONSTANT:
        out << tm.arithmetic_constant_value(t);
        break;

    case terms::Kind::ARITH_BINEQ_ATOM: {
        out << "(= ";
        pretty_print_term(args[0], tm, out);
        out << " ";
        pretty_print_term(args[1], tm, out);
        out << ")";
        break;
    }

    case terms::Kind::ARITH_EQ_ATOM:
        out << "(= ";
        pretty_print_term(args[0], tm, out);
        out << " ";
        pretty_print_term(args[1], tm, out);
        out << ")";
        break;

    case terms::Kind::ARITH_GE_ATOM:
        out << "(>= ";
        pretty_print_term(args[0], tm, out);
        out << " 0)";
        break;

    case terms::Kind::ARITH_PRODUCT:
        out << "(* ";
        pretty_print_term(args[0], tm, out);
        out << " ";
        pretty_print_term(args[1], tm, out);
        out << ")";
        break;

    case terms::Kind::ARITH_POLY:
        out << "(+";
        for (const auto& arg : args) {
            out << " ";
            pretty_print_term(arg, tm, out);
        }
        out << ")";
        break;

    case terms::Kind::OR_TERM:
        out << "(or";
        for (const auto& arg : args) {
            out << " ";
            pretty_print_term(arg, tm, out);
        }
        out << ")";
        break;

    case terms::Kind::XOR_TERM:
        out << "(xor";
        for (const auto& arg : args) {
            out << " ";
            pretty_print_term(arg, tm, out);
        }
        out << ")";
        break;

    case terms::Kind::APP_TERM: {
        std::string fname = std::string(tm.get_term_name(tm.get_fnc_symbol(t)).value_or("<?>"));
        out << "(" << fname;
        for (const auto& arg : args) {
            out << " ";
            pretty_print_term(arg, tm, out);
        }
        out << ")";
        break;
    }

    default:
        out << "<unknown>";
        break;
    }
}
} // namespace yaga::utils