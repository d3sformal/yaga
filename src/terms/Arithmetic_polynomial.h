#ifndef YAGA_ARITHMETIC_POLYNOMIAL_H
#define YAGA_ARITHMETIC_POLYNOMIAL_H

#include <vector>
#include <unordered_map>
#include <functional>
#include <iostream>

#include "Rational.h"

namespace yaga {


inline bool is_zero(Rational const& r)
{
    return r == 0;
}

template <typename TVar> class Polynomial {
private:
    struct Term {
        TVar var;
        Rational coeff;

        Term(TVar var, Rational&& coeff) : var{var.x}, coeff{std::move(coeff)} {}
    };

    struct Term_comparator {
        bool operator()(Term const& first, Term const& second)
        {
            return first.var < second.var;
        }
    };

public:
    using poly_t = std::vector<Term>; // Terms are ordered by variable num
private:
    poly_t poly;
    using mergeFunctionInformerType = void (*)(TVar);

public:
    void add_term(TVar var, Rational coeff);
    std::size_t size() const;
    Rational & get_coeff(TVar var) const;
    Rational remove_var(TVar var);
    void negate();
    void divide_by(Rational const& r);
    void multiply_by(Rational const& r);

    template <typename ADD = mergeFunctionInformerType, typename REM = mergeFunctionInformerType>
    void merge(
        Polynomial const& other, Rational const& coeff, poly_t& tmp_storage,
        ADD informAdded = [](TVar) {}, REM informRemoved = [](TVar) {});

    /* Simple version of merge that does not use the hooks and does not need external temporary storage */
    void merge(Polynomial const& other, Rational const& coeff)
    {
        poly_t tmp_storage;
        return merge(other, coeff, tmp_storage);
    }

    using iterator = typename poly_t::iterator;
    using const_iterator = typename poly_t::const_iterator;

    iterator begin() { return poly.begin(); }
    iterator end() { return poly.end(); }

    const_iterator begin() const { return poly.cbegin(); }
    const_iterator end() const { return poly.cend(); }

    // debug
    bool contains(TVar var) const { return find_term_for_var(var) != poly.end(); }

    const_iterator find_term_for_var(TVar var) const
    {
        return std::find_if(poly.begin(), poly.end(),
                            [var](Term const& term) { return term.var == var; });
    }

    iterator find_term_for_var(TVar var)
    {
        return std::find_if(poly.begin(), poly.end(),
                            [var](Term const& term) { return term.var == var; });
    }

    void print() const;
};

template <typename TVar>
template <typename ADD, typename REM>
void Polynomial<TVar>::merge(Polynomial<TVar> const& other, Rational const& coeff,
                                 poly_t& tmp_storage, ADD informAdded, REM informRemoved)
{
    if (tmp_storage.size() < this->poly.size() + other.poly.size())
    {
        tmp_storage.resize(this->poly.size() + other.poly.size(), Term(TVar::Undef, 0));
    }
    std::size_t storageIndex = 0;
    auto myIt = std::make_move_iterator(poly.begin());
    auto otherIt = other.poly.cbegin();
    auto myEnd = std::make_move_iterator(poly.end());
    auto otherEnd = other.poly.cend();
    Term_comparator cmp;
    Rational tmp{0};
    while (true)
    {
        if (myIt == myEnd)
        {
            for (auto it = otherIt; it != otherEnd; ++it)
            {
                tmp_storage[storageIndex].var = it->var;
                multiplication(tmp_storage[storageIndex].coeff, it->coeff, coeff);
                ++storageIndex;
                informAdded(it->var);
            }
            break;
        }
        if (otherIt == otherEnd)
        {
            std::move(myIt, myEnd, tmp_storage.begin() + storageIndex);
            storageIndex += myEnd - myIt;
            break;
        }
        if (cmp(*myIt, *otherIt))
        {
            tmp_storage[storageIndex] = *myIt;
            ++storageIndex;
            ++myIt;
        }
        else if (cmp(*otherIt, *myIt))
        {
            tmp_storage[storageIndex].var = otherIt->var;
            multiplication(tmp_storage[storageIndex].coeff, otherIt->coeff, coeff);
            ++storageIndex;
            informAdded(otherIt->var);
            ++otherIt;
        }
        else
        {
            assert(myIt->var == otherIt->var);
            multiplication(tmp, otherIt->coeff, coeff);
            myIt->coeff += tmp;
            if (is_zero(myIt->coeff))
            {
                informRemoved(myIt->var);
            }
            else
            {
                tmp_storage[storageIndex] = *myIt;
                ++storageIndex;
            }
            ++myIt;
            ++otherIt;
        }
    }
    // At this point the right elements are in `tmp_storage`, from beginning to the `storageIndex`.
    // We need to get these elements to `this->poly`. Note that we never change the `tmp_storage` container, we just move out the appropriate elements. However, we observed that we need to shrink `poly` if its size is much smaller than the capacity. The reason is that keeping large free capacity around for many rows blows up the memory (worse case quadratic in the size of the tableau).
    auto polySize = poly.size();
    if (storageIndex > polySize)
    {
        // In this case we have more elements to move than the current size of the `poly` container.
        // We move the elements that fit the current `poly` size and then we insert the rest of the elements.
        std::move(tmp_storage.begin(), tmp_storage.begin() + polySize, poly.begin());
        poly.insert(poly.end(), std::make_move_iterator(tmp_storage.begin() + polySize),
                    std::make_move_iterator(tmp_storage.begin() + storageIndex));
    }
    else if (/*storageIndex <= poly.size() and */ polySize <= 2 * storageIndex)
    {
        // In this case we have less elements that need to move than what we currently already have in `poly`, but not too litle. We just move the appropriate elements and destroy the excess elements of `poly`. Since we are removing too many elements, we avoid shrinking which would require re-allocation.
        std::move(tmp_storage.begin(), tmp_storage.begin() + storageIndex, poly.begin());
        poly.erase(poly.begin() + storageIndex, poly.end());
    }
    else
    { // poly.size() > 2 * storageIndex
        // This case is similar to case 2, but we have much less elements in the result than currently in `poly`. To avoid too large free capacity in `poly`, we shrink its capacity to exactly the number of elements. It is basically `poly.shrink_to_fit()`, except that `shrink_to_fit` is non-binding.
        std::vector<Term>(std::make_move_iterator(tmp_storage.begin()),
                          std::make_move_iterator(tmp_storage.begin() + storageIndex))
            .swap(poly);
    }
}

template <typename TVar> void Polynomial<TVar>::add_term(TVar var, Rational coeff)
{
    assert(!contains(var));
    Term term{var, std::move(coeff)};
    auto it = std::upper_bound(poly.begin(), poly.end(), term, Term_comparator{});
    poly.insert(it, std::move(term));
}

template <typename TVar> unsigned long Polynomial<TVar>::size() const { return poly.size(); }

template <typename TVar> Rational& Polynomial<TVar>::get_coeff(TVar var) const
{
    assert(contains(var));
    return find_term_for_var(var)->coeff;
}

template <typename TVar> Rational Polynomial<TVar>::remove_var(TVar var)
{
    assert(contains(var));
    iterator it = find_term_for_var(var);
    auto coeff = std::move(it->coeff);
    poly.erase(it);
    return coeff;
}

template <typename TVar> void Polynomial<TVar>::negate()
{
    for (auto& term : poly)
    {
        term.coeff = -term.coeff;
    }
}

template <typename TVar> void Polynomial<TVar>::divide_by(Rational const& r)
{
    for (auto& term : poly)
    {
        term.coeff /= r;
    }
}

template <typename TVar> void Polynomial<TVar>::multiply_by(Rational const& r)
{
    for (auto& term : poly)
    {
        term.coeff *= r;
    }
}

template <typename TVar> void Polynomial<TVar>::print() const
{
    for (auto& term : poly)
    {
        std::cout << term.coeff << " * " << term.var.x << "v + ";
    }
    std::cout << std::endl;
}

}
#endif // YAGA_ARITHMETIC_POLYNOMIAL_H
