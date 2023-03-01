#ifndef PERUN_FRACTION_H
#define PERUN_FRACTION_H

#include <cassert>
#include <cmath>
#include <concepts>
#include <cstdint>
#include <numeric>
#include <ostream>
#include <type_traits>

namespace perun {

class Normalized_tag {};

template <typename T>
    requires std::is_integral_v<T>
class Fraction {
public:
    inline constexpr Fraction() {}
    inline constexpr Fraction(T num) : num(num), denom(T{1}) {}
    inline constexpr Fraction(T num, T denom, Normalized_tag) : num(num), denom(denom) {}
    inline constexpr Fraction(T num, T denom)
        : Fraction((std::signbit(num) ^ std::signbit(denom) ? T{-1} : T{1}) * std::abs(num) /
                       std::gcd(num, denom),
                   std::abs(denom) / std::gcd(num, denom), Normalized_tag{})
    {
    }

    /** Convert a fraction of an Integer type to fraction of type T
     *
     * @tparam Integer integer type of numerator/denominator of @p other
     * @param other other fraction to convert
     */
    template <std::convertible_to<T> Integer>
        requires std::is_integral_v<Integer>
    inline constexpr Fraction(Fraction<Integer> other)
        : Fraction(static_cast<T>(other.numerator()), static_cast<T>(other.denominator()),
                   Normalized_tag{})
    {
    }

    /** Explicit conversion to an integer
     *
     * @tparam T integer type to convert to
     * @return integer representation of this value (possibly rounded down to the nearest integer)
     */
    template <typename Integer>
        requires std::is_integral_v<Integer>
    inline explicit operator Integer() const
    {
        return static_cast<Integer>(numerator() / denominator());
    }

    /** Add @p other to this fraction
     *
     * @tparam Integer type of numerator/denominator in @p other
     * @param other other fraction
     * @return this fraction
     */
    template <std::convertible_to<T> Integer>
    inline Fraction<T>& operator+=(Fraction<Integer> other)
    {
        auto res = *this + other;
        num = res.num;
        denom = res.denom;
        return *this;
    }

    /** Subtract @p other from this fraction
     *
     * @tparam Integer type of numerator/denominator in @p other
     * @param other other fraction
     * @return this fraction
     */
    template <std::convertible_to<T> Integer>
    inline Fraction<T>& operator-=(Fraction<Integer> other)
    {
        auto res = *this - other;
        num = res.num;
        denom = res.denom;
        return *this;
    }

    /** Multiply this fraction by @p other
     *
     * @tparam Integer type of numerator/denominator in @p other
     * @param other other fraction
     * @return this fraction
     */
    template <std::convertible_to<T> Integer>
    inline Fraction<T>& operator*=(Fraction<Integer> other)
    {
        auto res = *this * other;
        num = res.num;
        denom = res.denom;
        return *this;
    }

    /** Divide this fraction by @p other
     *
     * @tparam Integer type of numerator/denominator in @p other
     * @param other other fraction
     * @return this fraction
     */
    template <std::convertible_to<T> Integer>
    inline Fraction<T>& operator/=(Fraction<Integer> other)
    {
        auto res = *this / other;
        num = res.num;
        denom = res.denom;
        return *this;
    }

    /** Get numerator of the fraction
     *
     * @return numerator of the fraction
     */
    inline T numerator() const { return num; }

    /** Denominator of the fraction
     *
     * @return denominator of the fraction
     */
    inline T denominator() const { return denom; }

    /** Create an inverse of this fraction
     *
     * @return new fraction which represents inverse of this fraction
     */
    inline Fraction<T> inv() const
    {
        return {(std::signbit(num) ? T{-1} : T{1}) * denom, std::abs(num), Normalized_tag{}};
    }

private:
    T num;
    T denom;
};

namespace literals {

/** Convert an integer literal to a rational number (fraction)
 *
 * @param val value to convert
 * @return fraction which represents @p val
 */
inline constexpr Fraction<int> operator"" _r(unsigned long long val)
{
    return {static_cast<int>(val), 1, Normalized_tag{}};
}

} // namespace literals

/** Check whether a product of integers of type L and type R fits into type Prod
 *
 * @tparam L type of the first integer
 * @tparam R type of the second integer
 * @tparam Prod type of the product
 */
template <typename L, typename R, typename Prod>
    requires std::is_integral_v<L> && std::is_integral_v<R> && std::is_integral_v<Prod>
inline static constexpr bool product_fits_in = sizeof(L) + sizeof(R) <= sizeof(Prod);

/** Print a fraction to an output stream
 *
 * @param out output stream
 * @param frac fraction to print
 * @return @p out
 */
template <typename T>
    requires std::is_integral_v<T>
inline std::ostream& operator<<(std::ostream& out, Fraction<T> frac)
{
    if (frac.denominator() == 1)
    {
        out << frac.numerator();
    }
    else
    {
        out << frac.numerator() << "/" << frac.denominator();
    }
    return out;
}

/** Compare two fractions
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the second fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs == @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator==(Fraction<L> lhs, Fraction<R> rhs)
{
    auto lhs_num = static_cast<std::common_type_t<L, R>>(lhs.numerator());
    auto rhs_num = static_cast<std::common_type_t<L, R>>(rhs.numerator());
    auto lhs_denom = static_cast<std::common_type_t<L, R>>(lhs.denominator());
    auto rhs_denom = static_cast<std::common_type_t<L, R>>(rhs.denominator());
    return lhs_num == rhs_num && lhs_denom == rhs_denom;
}

/** Compare two fractions
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the second fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs != @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator!=(Fraction<L> lhs, Fraction<R> rhs)
{
    return !operator==(lhs, rhs);
}

/** Check whether @p lhs < @p rhs
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the first fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs < @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R> && product_fits_in<L, R, std::int64_t>
inline bool operator<(Fraction<L> lhs, Fraction<R> rhs)
{
    auto lhs_val = static_cast<std::int64_t>(lhs.numerator()) * rhs.denominator();
    auto rhs_val = static_cast<std::int64_t>(rhs.numerator()) * lhs.denominator();
    return lhs_val < rhs_val;
}

/** Check whether @p lhs <= @p rhs
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the first fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs <= @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R> && product_fits_in<L, R, std::int64_t>
inline bool operator<=(Fraction<L> lhs, Fraction<R> rhs)
{
    auto lhs_val = static_cast<std::int64_t>(lhs.numerator()) * rhs.denominator();
    auto rhs_val = static_cast<std::int64_t>(rhs.numerator()) * lhs.denominator();
    return lhs_val <= rhs_val;
}

/** Check whether @p lhs > @p rhs
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the first fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs > @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator>(Fraction<L> lhs, Fraction<R> rhs)
{
    return !operator<=(lhs, rhs);
}

/** Check whether @p lhs >= @p rhs
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the first fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs > @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator>=(Fraction<L> lhs, Fraction<R> rhs)
{
    return !operator<(lhs, rhs);
}

/** Check whether @p lhs <= @p rhs
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of an integer constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return true iff @p lhs <= @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R> && product_fits_in<L, R, std::int64_t>
inline bool operator<=(Fraction<L> lhs, R rhs)
{
    return lhs.numerator() <= static_cast<std::int64_t>(lhs.denominator()) * rhs;
}

/** Check whether @p lhs < @p rhs
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of an integer constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return true iff @p lhs < @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R> && product_fits_in<L, R, std::int64_t>
inline bool operator<(Fraction<L> lhs, R rhs)
{
    return lhs.numerator() < static_cast<std::int64_t>(lhs.denominator()) * rhs;
}

/** Check whether @p lhs >= @p rhs
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of an integer constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return true iff @p lhs >= @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator>=(Fraction<L> lhs, R rhs)
{
    return !operator<(lhs, rhs);
}

/** Check whether @p lhs > @p rhs
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of an integer constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return true iff @p lhs > @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator>(Fraction<L> lhs, R rhs)
{
    return !operator<=(lhs, rhs);
}

/** Compare fraction and an integer constant
 *
 * @tparam L type of numerator/denominator of the fraction
 * @tparam R type of the constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return true iff @p lhs == @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator==(Fraction<L> lhs, R rhs)
{
    auto lhs_val = static_cast<std::common_type_t<L, R>>(lhs.numerator());
    auto rhs_val = static_cast<std::common_type_t<L, R>>(rhs);
    return lhs.denominator() == L{1} && lhs_val == rhs_val;
}

/** Compare fraction and an integer constant
 *
 * @tparam L type of numerator/denominator of the fraction
 * @tparam R type of the constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return true iff @p lhs == @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator!=(Fraction<L> lhs, R rhs)
{
    return !operator==(lhs, rhs);
}

/** Check whether @p lhs <= @p rhs
 *
 * @tparam L type of an integer constant
 * @tparam R type of numerator/denominator of the fraction
 * @param lhs constant on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs <= @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator<=(L lhs, Fraction<R> rhs)
{
    return rhs >= lhs;
}

/** Check whether @p lhs < @p rhs
 *
 * @tparam L type of an integer constant
 * @tparam R type of numerator/denominator of the fraction
 * @param lhs constant on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs < @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator<(L lhs, Fraction<R> rhs)
{
    return rhs > lhs;
}

/** Check whether @p lhs >= @p rhs
 *
 * @tparam L type of an integer constant
 * @tparam R type of numerator/denominator of the fraction
 * @param lhs constant on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs >= @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator>=(L lhs, Fraction<R> rhs)
{
    return rhs <= lhs;
}

/** Check whether @p lhs > @p rhs
 *
 * @tparam L type of an integer constant
 * @tparam R type of numerator/denominator of the fraction
 * @param lhs constant on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return true iff @p lhs > @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline bool operator>(L lhs, Fraction<R> rhs)
{
    return rhs < lhs;
}

/** Create a negation of a fraction
 *
 * @tparam Integer type of numerator/denominator of the fraction
 * @param frac fraction to negation
 * @return negation of @p frac
 */
template <typename Integer>
    requires std::is_integral_v<Integer>
inline Fraction<Integer> operator-(Fraction<Integer> frac)
{
    return {-frac.numerator(), frac.denominator(), Normalized_tag{}};
}

/** Add two fractions
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the second fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return new fraction which represents @p lhs + @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R> && product_fits_in<L, R, std::int64_t>
inline Fraction<std::common_type_t<L, R>> operator+(Fraction<L> lhs, Fraction<R> rhs)
{
    std::int64_t lhs_num = lhs.numerator();
    std::int64_t rhs_num = rhs.numerator();
    std::int64_t num = lhs_num * rhs.denominator() + rhs_num * lhs.denominator();
    std::int64_t denom = static_cast<std::int64_t>(lhs.denominator()) * rhs.denominator();
    std::int64_t gcd = std::gcd(num, denom);
    num /= gcd;
    denom /= gcd;
    assert(std::numeric_limits<int>::lowest() <= num);
    assert(num <= std::numeric_limits<int>::max());
    assert(std::numeric_limits<int>::lowest() <= denom);
    assert(denom <= std::numeric_limits<int>::max());
    return {static_cast<int>(num), static_cast<int>(denom), Normalized_tag{}};
}

/** Subtract two fractions
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the second fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return new fraction which represents @p lhs - @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator-(Fraction<L> lhs, Fraction<R> rhs)
{
    return lhs + (-rhs);
}

/** Multiply two fractions
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the second fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return new fraction which represents @p lhs * @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R> && product_fits_in<L, R, std::int64_t>
inline Fraction<std::common_type_t<L, R>> operator*(Fraction<L> lhs, Fraction<R> rhs)
{
    std::int64_t num = static_cast<std::int64_t>(lhs.numerator()) * rhs.numerator();
    std::int64_t denom = static_cast<std::int64_t>(lhs.denominator()) * rhs.denominator();
    std::int64_t gcd = std::gcd(num, denom);
    num /= gcd;
    denom /= gcd;
    assert(std::numeric_limits<int>::lowest() <= num);
    assert(num <= std::numeric_limits<int>::max());
    assert(std::numeric_limits<int>::lowest() <= denom);
    assert(denom <= std::numeric_limits<int>::max());
    return {static_cast<int>(num), static_cast<int>(denom), Normalized_tag{}};
}

/** Divide two fractions
 *
 * @tparam L type of numerator/denominator of the first fraction
 * @tparam R type of numerator/denominator of the second fraction
 * @param lhs fraction on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return new fraction which represents @p lhs / @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator/(Fraction<L> lhs, Fraction<R> rhs)
{
    return lhs * rhs.inv();
}

/** Add a fraction and an integer constant
 *
 * @tparam L type of numerator/denominator of the fraction
 * @tparam R type of the constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return new fraction which represents @p lhs + @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator+(Fraction<L> lhs, R rhs)
{
    return lhs + Fraction<R>{rhs};
}

/** Subtract an integer constant from a fraction
 *
 * @tparam L type of numerator/denominator of the fraction
 * @tparam R type of the constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return new fraction which represents @p lhs - @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator-(Fraction<L> lhs, R rhs)
{
    return lhs + (-rhs);
}

/** Multiply a fraction by an integer constant
 *
 * @tparam L type of numerator/denominator of the fraction
 * @tparam R type of the constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return new fraction which represents @p lhs * @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator*(Fraction<L> lhs, R rhs)
{
    return lhs * Fraction<R>{rhs};
}

/** Divide a fraction by an integer constant
 *
 * @tparam L type of numerator/denominator of the fraction
 * @tparam R type of the constant
 * @param lhs fraction on the left-hand-side
 * @param rhs constant on the right-hand-side
 * @return new fraction which represents @p lhs / @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator/(Fraction<L> lhs, R rhs)
{
    return lhs / Fraction<R>{rhs};
}

/** Add a fraction and an integer constant
 *
 * @tparam L type of the constant
 * @tparam R type of numerator/denominator of the fraction
 * @param lhs constant on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return new fraction which represents @p lhs + @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator+(L lhs, Fraction<R> rhs)
{
    return rhs + lhs;
}

/** Subtract fraction from an integer constant
 *
 * @tparam L type of the constant
 * @tparam R type of numerator/denominator of the fraction
 * @param lhs constant on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return new fraction which represents @p lhs - @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator-(L lhs, Fraction<R> rhs)
{
    return lhs + (-rhs);
}

/** Multiply fraction by an integer constant
 *
 * @tparam L type of the constant
 * @tparam R type of numerator/denominator of the fraction
 * @param lhs constant on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return new fraction which represents @p lhs * @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator*(L lhs, Fraction<R> rhs)
{
    return rhs * lhs;
}

/** Divide an integer constant by a fraction
 *
 * @tparam L type of the constant
 * @tparam R type of numerator/denominator of the fraction
 * @param lhs constant on the left-hand-side
 * @param rhs fraction on the right-hand-side
 * @return new fraction which represents @p lhs / @p rhs
 */
template <typename L, typename R>
    requires std::is_integral_v<L> && std::is_integral_v<R>
inline Fraction<std::common_type_t<L, R>> operator/(L lhs, Fraction<R> rhs)
{
    return lhs * rhs.inv();
}

} // namespace perun

namespace std {

template <typename T>
    requires std::is_integral_v<T>
class numeric_limits<perun::Fraction<T>> {
public:
    inline static constexpr bool is_specialized = true;
    inline static constexpr bool is_signed = std::numeric_limits<T>::is_signed;
    inline static constexpr bool is_integer = false;
    inline static constexpr bool is_exact = true;
    inline static constexpr bool has_infinity = false;
    inline static constexpr bool has_quiet_NaN = false;
    inline static constexpr bool has_signaling_NaN = false;
    inline static constexpr bool has_denorm = false;
    inline static constexpr bool has_denorm_loss = false;
    inline static constexpr std::float_round_style round_style =
        std::float_round_style::round_toward_zero;
    inline static constexpr bool is_iec559 = false;
    inline static constexpr bool is_bounded = true;
    inline static constexpr bool is_modulo = std::numeric_limits<T>::is_modulo;
    inline static constexpr int digits = std::numeric_limits<T>::digits;
    inline static constexpr int digits10 = std::numeric_limits<T>::digits10;
    inline static constexpr int min_exponent = std::numeric_limits<T>::min_exponent;
    inline static constexpr int min_exponent10 = std::numeric_limits<T>::min_exponent10;
    inline static constexpr bool traps = std::numeric_limits<T>::traps;
    inline static constexpr bool tinyness_before = false;

    inline static constexpr perun::Fraction<T> min() { return std::numeric_limits<T>::min(); }
    inline static constexpr perun::Fraction<T> lowest() { return std::numeric_limits<T>::lowest(); }
    inline static constexpr perun::Fraction<T> max() { return std::numeric_limits<T>::max(); }
    inline static constexpr perun::Fraction<T> epsilon()
    {
        return std::numeric_limits<T>::epsilon();
    }
};

template <typename T>
    requires std::is_integral_v<T>
struct common_type<perun::Fraction<T>, T> {
    using type = perun::Fraction<T>;
};

template <typename T>
    requires std::is_integral_v<T>
struct common_type<T, perun::Fraction<T>> {
    using type = perun::Fraction<T>;
};

template <typename T>
    requires std::is_integral_v<T> && (2 * sizeof(T) <= sizeof(std::uint64_t))
struct hash<perun::Fraction<T>> {
    inline std::size_t operator()(perun::Fraction<T> frac) const
    {
        return std::hash<std::uint64_t>{}((static_cast<std::uint64_t>(frac.numerator()) << 32) |
                                          static_cast<std::uint64_t>(frac.denominator()));
    }
};

} // namespace std

#endif // PERUN_FRACTION_H