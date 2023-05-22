#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "Smt2_parser.h"

using namespace yaga;


int main(int argc, char** argv)
{
    if (argc != 2)
    {
        std::cerr << "Usage: ./smt [input-path.smt2]" << std::endl;
        return -1;
    }

    parser::Smt2_parser parser;
    parser.parse_file(argv[1]);
}