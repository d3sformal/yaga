//
// Created by kofron on 5.4.23.
//

#ifndef YAGA_RATIONAL_H
#define YAGA_RATIONAL_H

//#include "Fraction.h"
#include "Long_fraction.h"

namespace yaga {
        using Rational = Long_fraction;
        //using Rational = Fraction<int>;

    namespace literals {

/** Convert an integer literal to a rational number (fraction)
*
* @param val value to convert
* @return fraction which represents @p val
*/
        inline constexpr Rational operator ""_r(unsigned long long int val) {
            assert(val <= std::numeric_limits<int>::max());
            int int_val = static_cast<int>(val);
            return Rational(int_val);
        }
    }

}


#endif //YAGA_RATIONAL_H
