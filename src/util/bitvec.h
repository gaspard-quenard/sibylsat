#ifndef BITVEC_H
#define BITVEC_H
#include <vector>
#include <cstdint>

struct BitVec
{
    using Block = uint64_t;
    std::vector<Block> v;

    explicit BitVec(size_t n = 0) : v((n + 63) >> 6, 0) {}

    BitVec(std::size_t n, bool fill)
        : v((n + 63) >> 6, fill ? ~Block(0) : Block(0))
    {
        if (fill && (n & 63))
        {                                      // partial last word?
            std::size_t used = n & 63;         // 1-to-63 meaningful bits
            v.back() = (Block(1) << used) - 1; // keep only those bits = 1
        }
    }

    inline void set(int b) { v[b >> 6] |= Block(1) << (b & 63); }
    inline bool test(int b) const { return v[b >> 6] & (Block(1) << (b & 63)); }

    /* OR / AND / MINUS  (return true if changed) ------------------------ */
    bool or_with(const BitVec &o)
    {
        bool ch = false;
        for (size_t i = 0; i < v.size(); ++i)
        {
            auto x = v[i] | o.v[i];
            ch |= x != v[i];
            v[i] = x;
        }
        return ch;
    }
    bool and_with(const BitVec &o)
    {
        bool ch = false;
        for (size_t i = 0; i < v.size(); ++i)
        {
            auto x = v[i] & o.v[i];
            ch |= x != v[i];
            v[i] = x;
        }
        return ch;
    }
    void minus_with(const BitVec &o)
    {
        for (size_t i = 0; i < v.size(); ++i)
            v[i] &= ~o.v[i];
    }

    bool none() const
    { // true ⇔ every bit is 0
        for (Block b : v)
            if (b)
                return false;
        return true;
    }
    bool any() const { return !none(); }

    /* number of 1-bits in the whole vector */
    std::size_t count() const
    {
        std::size_t s = 0;
#ifdef __GNUG__ // GCC / Clang
        for (Block b : v)
            s += __builtin_popcountll(b);
#else // C++20 alternative
        for (Block b : v)
            s += std::popcount(b);
#endif
        return s;
    }

    // Turn one specific bit off
    inline void clear(int bit) { v[bit >> 6] &= ~(Block(1) << (bit & 63)); }

    /* iterate over all set bits, calling F(int bit) */
    template <class F>
    void for_each_set(F f) const
    {
        for (size_t w = 0; w < v.size(); ++w) // every 64-bit word
        {
            Block word = v[w]; // copy of the word
            while (word)       // until no 1s left
            {
                int b = std::countr_zero(word); // index of lowest 1-bit
                f(int(w * 64 + b));             // call the callback

                word &= word - 1; // clear **that** 1-bit
            }
        }
    }

    class const_iterator
    {
        const BitVec *_bv = nullptr;
        std::size_t _word = 0; // index in v
        Block _mask = 0;       // remaining 1-bits in current word
        std::size_t _bit = 0;  // absolute bit index of next value

        void advance()
        {
            while (!_mask)
            {
                if (++_word >= _bv->v.size())
                {
                    _bv = nullptr; // ← sentinel
                    _bit = 0;      // ← reset to make == work
                    return;
                }
                _mask = _bv->v[_word];
            }
            unsigned tz = std::countr_zero(_mask);
            _bit = (_word << 6) + tz;
            _mask &= _mask - 1;
        }

    public:
        /* construct begin() */
        explicit const_iterator(const BitVec *bv)
            : _bv(bv), _mask(bv && !bv->v.empty() ? bv->v[0] : 0)
        {
            if (_bv)
                advance(); // find the first 1-bit or end
        }
        /* construct end()  */
        const_iterator() = default;

        /* STL iterator boiler-plate */
        using iterator_category = std::forward_iterator_tag;
        using value_type = std::size_t;
        using reference = std::size_t;
        using pointer = void;
        using difference_type = std::ptrdiff_t;

        std::size_t operator*() const { return _bit; }

        const_iterator &operator++()
        {
            advance();
            return *this;
        }
        const_iterator operator++(int)
        {
            const_iterator tmp = *this;
            ++*this;
            return tmp;
        }

        bool operator==(const const_iterator &o) const { return _bv == o._bv; }
        bool operator!=(const const_iterator &o) const { return !(*this == o); }
    };

    /* range helpers */
    const_iterator begin() const { return const_iterator(this); }
    const_iterator end() const { return const_iterator(); }
};

#endif // BITVEC_H