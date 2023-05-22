/*
Fast rationals
David Monniaux, VERIMAG 2008-2009

Copyright (c) 2008, 2009 Centre national de la recherche scientifique (CNRS)

Available under the MIT license.

Modifications:
Antti Hyvarinen (Univerzita Svizzera italiana Lugano)
Martin Blicha  (Univerzita Svizzera italiana Lugano)
Jan Kofron (Charles University, Prague)
 */
#include "Long_fraction.h"
#include <sstream>
#include <algorithm>

namespace yaga {

    mpq_ptr Long_fraction::mpqPool::alloc() {
        mpq_ptr r;
        if (!pool.empty()) {
            r = pool.top();
            pool.pop();
        } else {
            r = store.emplace().get_mpq_t();
        }
        return r;
    }

    void Long_fraction::mpqPool::release(mpq_ptr ptr) {
        pool.push(ptr);
    }

    Long_fraction::Long_fraction(const char *s, const int base) {
        mpq = pool.alloc();
        mpq_set_str(mpq, s, base);
        mpq_canonicalize(mpq);
        state = State::MPQ_ALLOCATED_AND_VALID;
        try_fit_word();
        if (wordPartValid())
            kill_mpq();
        assert(isWellFormed());
    }

    Long_fraction::Long_fraction(mpz_t z) {
        if (mpz_fits_sint_p(z)) {
            num = mpz_get_si(z);
            den = 1;
            state = State::WORD_VALID;
        } else {
            mpq = pool.alloc();
            mpz_set(mpq_numref(mpq), z);
            mpz_set_ui(mpq_denref(mpq), 1);
            state = State::MPQ_ALLOCATED_AND_VALID;
        }
    }

    Long_fraction::Long_fraction(uint32_t x)  {
        if (x > INT_MAX) {
            mpq = pool.alloc();
            mpq_set_ui(mpq, x, 1);
            state = State::MPQ_ALLOCATED_AND_VALID;
        } else {
            num = x;
            den = 1;
            state = State::WORD_VALID;
        }
    }



    void Long_fraction::reset() {
        kill_mpq();
        state = State::WORD_VALID;
        num = 0;
        den = 1;
    }

    void Long_fraction::print(std::ostream &out) const {
        const bool sign = this->sign() < 0;
        if (wordPartValid()) {
            uword abs_num = absVal(num);
            if (den == 1) {
                out << (sign ? "(- " : "") << abs_num << (sign ? ")" : "");
            } else {
                out << "(/ " << (sign ? "(- " : "") << abs_num << (sign ? ") " : " ") << den << ")";
            }
        } else {
            assert(mpqPartValid());
            mpq_class mpq_c(mpq);
            if (sign) mpq_c = -mpq_c;
            out << (sign ? "(- " : "") << mpq_c << (sign ? ")" : "");
        }
    }

    void Long_fraction::print_(std::ostream &out) const {
        if (wordPartValid()) {
            if (den == 1) {
                out << num;
            } else {
                out << num << "/" << den;
            }
        } else {
            assert(mpqPartValid());
            out << mpq;
        }
    }

    std::string Long_fraction::get_str() const {
        std::ostringstream os;
        print_(os);
        return os.str();
    }

    Long_fraction gcd(Long_fraction const &a, Long_fraction const &b) {
        assert(a.isInteger() and b.isInteger());
        if (a.wordPartValid() && b.wordPartValid()) {
            return Long_fraction(gcd(a.num, b.num));
        } else {
            a.force_ensure_mpq_valid();
            b.force_ensure_mpq_valid();
            mpz_gcd(Long_fraction::mpz(), mpq_numref(a.mpq), mpq_numref(b.mpq));
            return Long_fraction(Long_fraction::mpz());
        }
    }

    Long_fraction lcm(Long_fraction const &a, Long_fraction const &b) {
        assert(a.isInteger() and b.isInteger());
        if (a.wordPartValid() && b.wordPartValid()) {
            return lcm(a.num, b.num);
        } else {
            a.force_ensure_mpq_valid();
            b.force_ensure_mpq_valid();
            mpz_lcm(Long_fraction::mpz(), mpq_numref(a.mpq), mpq_numref(b.mpq));
            return Long_fraction(Long_fraction::mpz());
        }
    }

    Long_fraction fastrat_round_to_int(const Long_fraction &n) {
        Long_fraction res = n + Long_fraction(1, 2);
        return fastrat_fdiv_q(res.get_num(), res.get_den());
    }

// The quotient of n and d using the fast rationals.
// Divide n by d, forming a quotient q.
// Rounds q down towards -infinity, and q will satisfy n = q*d + r for some 0 <= abs(r) <= abs(d)
    Long_fraction fastrat_fdiv_q(Long_fraction const &n, Long_fraction const &d) {
        assert(n.isInteger() && d.isInteger());
        if (n.wordPartValid() && d.wordPartValid()) {
            word num = n.num;
            word den = d.num;
            word quo;
            if (num == INT_MIN) // The abs is guaranteed to overflow.  Otherwise this is always fine
                goto overflow;
            // After this -INT_MIN+1 <= numerator <= INT_MAX, and therefore the result always fits into a word.
            quo = num / den;
            if (num % den != 0 && ((num < 0 && den >= 0) || (den < 0 && num >= 0))) // The result should be negative
                quo--; // INT_MAX-1 >= quo >= -INT_MIN

            return quo;
        }
        overflow:
        n.force_ensure_mpq_valid();
        d.force_ensure_mpq_valid();
        mpz_fdiv_q(Long_fraction::mpz(), mpq_numref(n.mpq), mpq_numref(d.mpq));
        return Long_fraction(Long_fraction::mpz());
    }

//void mpz_divexact (mpz_ptr, mpz_srcptr, mpz_srcptr);
    Long_fraction divexact(Long_fraction const &n, Long_fraction const &d) {
        assert(d != 0);
        assert(n.isInteger() && d.isInteger());
        if (n.wordPartValid() && d.wordPartValid()) {
            word num = n.num;
            word den = d.num;
            word quo;
            if (den != 0) {
                quo = num / den;
                return quo;
            } else {
                // Division by zero
                assert(false);
                return Long_fraction(0);
            }
        } else {
            assert(n.mpqPartValid() || d.mpqPartValid());
            n.force_ensure_mpq_valid();
            d.force_ensure_mpq_valid();
            mpz_divexact(Long_fraction::mpz(), mpq_numref(n.mpq), mpq_numref(d.mpq));
            return Long_fraction(Long_fraction::mpz());
        }
    }

// Given as input the sequence Reals, return the smallest number m such that for each r in Reals, r*m is an integer
    Long_fraction get_multiplicand(const std::vector<Long_fraction> &reals) {
        std::vector<Long_fraction> dens;
        for (const auto &r: reals) {
            if (!r.isInteger()) {
                dens.push_back(r.get_den());
            }
        }

        // Iterate until dens is not empty
        Long_fraction mult = 1; // Collect here the number I need to multiply the polynomial to get rid of all denominators
        while (dens.size() > 0) {
            // Unique denominators
            std::sort(dens.begin(), dens.end());
            auto last = std::unique(dens.begin(), dens.end());
            dens.erase(last, dens.end());
#ifdef PRINTALOT
            char *buf = (char*) malloc(1);
            buf[0] = '\0';
            char *buf_new;

            for (int j = 0; j < dens.size(); j++) {
                asprintf(&buf_new, "%s%s%s", buf, dens[j].get_str().c_str(),
                         j == dens.size() - 1 ? "" : ", ");
                free(buf);
                buf = buf_new;
            }
            printf("Dens size now %lu, and individual are denominators: %s\n", dens.size(), buf);
            free(buf);
#endif
            if (dens.size() == 1) {
                mult *= dens[0];
                dens.clear();
            } else {
                // We filter in place the integers in dens.  The last two are guaranteed to be ;
                int k = 0;
                Long_fraction m = lcm(dens[dens.size() - 1], dens[dens.size() - 2]);
                mult *= m;
                for (size_t j = 0; j < dens.size() - 2; j++) {
                    Long_fraction n = (m / dens[j]).get_den();
                    if (n != 1)
                        dens[k++] = n;
                }
                dens.resize(k);
            }
        }
#ifdef PRINTALOT
        printf("Multiplicand is %s\n", mult.get_str().c_str());
#endif
        return mult;
    }
}