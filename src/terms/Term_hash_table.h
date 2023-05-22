#ifndef YAGA_TERM_HASH_TABLE_H
#define YAGA_TERM_HASH_TABLE_H

#include "Term_types.h"

#include <span>
#include <unordered_set>

#include <Rational.h>

namespace yaga::terms {

class Term_table;

struct Term_hash_proxy
{
    Kind kind;
    type_t type;
    uint64_t hash;
    Term_table& term_table;

    Term_hash_proxy(Kind kind, type_t type, uint64_t hash, Term_table& termTable) :
        kind(kind), type(type), hash(hash), term_table(termTable) {}
};

struct Composite_term_proxy : public Term_hash_proxy
{
    std::span<term_t> args;

    Composite_term_proxy(Kind kind, type_t type, uint64_t hash, Term_table& termTable, std::span<term_t> args) :
        Term_hash_proxy(kind, type, hash, termTable), args(args) {}
};

struct Constant_term_proxy : public Term_hash_proxy
{
    int32_t index;

    Constant_term_proxy(Kind kind, type_t type, uint64_t hash, Term_table& termTable, int32_t index) :
        Term_hash_proxy(kind, type, hash, termTable), index(index) {}
};

struct Rational_proxy : public Term_hash_proxy
{
    Rational const & value;

    Rational_proxy(uint64_t hash, Term_table& termTable, Rational const& value) :
        Term_hash_proxy(Kind::ARITH_CONSTANT, types::real_type, hash, termTable), value(value) {}
};

class Term_hash_table {
public:
    [[nodiscard]] term_t get_composite_term(Composite_term_proxy const& proxy);
    [[nodiscard]] term_t get_rational_term(Rational_proxy const& proxy);
    [[nodiscard]] term_t get_constant_term(Constant_term_proxy const& proxy);

private:
    struct Entry {
        uint64_t hash;
        term_t term;
    };

    struct Hash {
        using is_transparent = void;
        uint64_t operator()(Entry const& entry) const { return entry.hash; }
        uint64_t operator()(Term_hash_proxy const& proxy) const { return proxy.hash; }
    };

    struct KeyEqual {
        using is_transparent = void;
        bool operator()(Entry const& proxy, Entry const& entry) const;
        bool operator()(Composite_term_proxy const& proxy, Entry const& entry) const;
        bool operator()(Constant_term_proxy const& proxy, Entry const& entry) const;
        bool operator()(Rational_proxy const& proxy, Entry const& entry) const;
    };

    std::unordered_set<Entry, Hash, KeyEqual> terms;
};

} // namespace yaga::terms

#endif // YAGA_TERM_HASH_TABLE_H
