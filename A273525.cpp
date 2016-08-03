/*
 * OEIS A273525: define
 *   S_0 = {0, 1}
 *   S_{n+1} = { sum(s)/size(s) for nonempty s \subseteq S_n }
 *
 * Then a_n = size(S_n).
 * It is easy to see that a_0 = 2, a_1 = 3, a_2 = 5, a_3 = 15, a_4 = 875.
 * This program calculates a_5.
 */

#include <cassert>
#include <cstdio>
#include <cinttypes>
#include <cmath>
#include <ctime>
#include <algorithm>
#include <vector>
#include <set>
#include <list>
#include <gmpxx.h>

using namespace std;

#define DEBUG(...) fprintf(stderr, "[debug] " __VA_ARGS__);
#define DEBUG_MORE(...) fprintf(stderr, __VA_ARGS__);

// We use a naïve method to calculate S_1...S_4.
set <mpq_class> next_naive(const set <mpq_class>& S)
{
    assert (S.size() < 64);
    vector <mpq_class> S_vec(S.begin(), S.end());
    set <mpq_class> S_next;
    for (uint64_t bit = 1; bit < uint64_t(1) << S.size(); ++bit) {
        mpq_class sum = 0;
        size_t size = 0;
        for (size_t i = 0; i < S.size(); ++i) {
            if (bit & (uint64_t(1) << i)) {
                ++size;
                sum += S_vec[i];
            }
        }
        S_next.insert(sum / size);
    }
    return S_next;
}

// Should be true on amd64; simplifies things
static_assert (GMP_NUMB_BITS >= 64, "GMPlib limb size");

uint64_t gcd(uint64_t a, uint64_t b) {
    if (a == 0) return b;
    if (b == 0) return a;
    mp_limb_t mp_a = a;
    return mpn_gcd_1(&mp_a, 1, b);
}
uint64_t lcm(uint64_t a, uint64_t b) {
    return a / gcd(a, b) * b;
}

static const size_t S_4_size = 875;
// Lowest common denominator of S_4.
// (All subset sums of S_4 can be represented with this denominator.)
static const uint64_t S_4_denom = 17297280;

/*
 * Integer (multi-)set data structure.
 * This stores a set of uint64_t values in sorted order.
 * The only operations supported are sorted-append and traverse
 * (element-wise operations such as union and set difference
 *  are easy to implement on top).
 *
 * We encode only the differences between the values. We use a
 * self-delimiting bytestream with the following formats:
 *   Prefix       Gap size
 *   0            7 bits
 *   10           14 bits
 *   11NNN000     next NNN+3 bytes
 * These prefixes are written with the least significant bit first.
 * Gap values are also stored little-endian.
 *
 * There is an upper bound of S_4_denom * S_4_size^2 = 8e12
 * elements of S_5 and estimate_a5 gives a (very inaccurate) guess
 * of |S_5| = 1.1e11, making the average gap size 80. So we expect
 * (hope? wish?) that most of the gaps will fit in 1 byte.
 */
struct IntSet {
    typedef uint64_t value_type;

    vector <uint8_t> stream_;
    size_t size_;
    value_type max_;

    struct iterator {
        const IntSet* set_;
        size_t pos_;
        uint64_t value_;

        iterator():
            set_(nullptr), pos_(0), value_(0) {
        }
        iterator(const iterator&) = default;
        iterator& operator=(const iterator&) = default;
        iterator(const IntSet& set):
            set_(&set), pos_(0), value_(0) {
        }

        iterator& operator++() {
            unsigned len;
            value_type val;
            tie(len, val) = decode();
            pos_ += len;
            value_ += val;
            return *this;
        }
        value_type operator*() const {
            return value_ + decode().second;
        }
        pair <unsigned, value_type> decode() const {
            assert (set_);
            assert (pos_ < set_->stream_.size());
            unsigned b0 = set_->stream_[pos_];
            if ((b0 & 0x1u) == 0) {
                return pair <unsigned, value_type> (1, b0 >> 1);
            } else if ((b0 & 0x3u) == 0x1u) {
                assert (pos_ + 1 < set_->stream_.size());
                unsigned b1 = set_->stream_[pos_ + 1];
                return pair <unsigned, value_type> (2, (b0 >> 2) | (b1 << 6));
            } else {
                assert ((b0 & 0x3u) == 0x3u);
                unsigned bytes = (b0 >> 2) + 3;
                assert (bytes >= 3 && bytes <= 8 && pos_ + bytes < set_->stream_.size());
                value_type val = 0;
                for (unsigned i = bytes; i > 0; --i) {
                    val = (val << 8) | set_->stream_[pos_ + i];
                }
                return pair <unsigned, value_type> (bytes + 1, val);
            }
        }
        bool operator==(const iterator& it) const {
            return set_ == it.set_ && pos_ == it.pos_;
        }
        bool operator!=(const iterator& it) const {
            return !operator==(it);
        }
    };

    IntSet():
        size_(0), max_(0) {
    }
    IntSet(const IntSet& set) = default;
    IntSet(IntSet&& set) = default;
    IntSet& operator=(const IntSet&) = default;
    IntSet& operator=(IntSet&&) = default;
    ~IntSet() = default;

    void push_back(value_type v) {
        assert (v >= max_);
        value_type d = v - max_;
        if (d < value_type(1) << 7) {
            stream_.push_back((d << 1) | 0x0u);
        } else if (d < value_type(1) << 14) {
            stream_.push_back((d << 2) | 0x1u);
            stream_.push_back(d >> 6);
        } else {
            unsigned sz = 24;
            for (; sz >= 64 || d >= value_type(1) << sz; sz += 8);
            stream_.push_back(0x3u + ((sz/8 - 3u) << 2));
            for (unsigned i = 0; i < sz; i += 8) {
                stream_.push_back(d >> i);
            }
        }
        max_ = v;
        ++size_;
    }
    size_t size() const {
        return size_;
    }
    iterator begin() const {
        return iterator(*this);
    }
    iterator end() const {
        iterator it(*this);
        it.pos_ = stream_.size();
        return it;
    }
    size_t space() const {
        return stream_.size();
    }
    size_t capacity() const {
        return stream_.capacity();
    }
    void swap(IntSet& set) {
        stream_.swap(set.stream_);
        std::swap(size_, set.size_);
        std::swap(max_, set.max_);
    }
};

/*
 * Chunked version of IntSet. Avoids memory allocation issues
 * for very large sets.
 */
struct ChunkedIntSet {
    typedef IntSet::value_type value_type;

    list <IntSet> chunks_;
    size_t size_;

    /* chunk_size_ is used in the following way:
     * Once the current chunk has surpassed chunk_size_, it continues
     * to be used up to its current capacity() - 8. The -8 term is
     * because storing the next value could require up to 9 bytes. */
    // 128K — gcc's resize policy typically rounds up to 256K
    static const size_t chunk_size_ = 1 << 17;
    static const size_t value_size_ = 9;

    struct iterator {
        list <IntSet>::const_iterator chunk_iter_, chunks_end_;
        IntSet::iterator val_iter_, vals_end_;

        iterator() = default;
        iterator(const ChunkedIntSet& set):
            chunk_iter_(set.chunks_.begin()), chunks_end_(set.chunks_.end()),
            val_iter_(chunk_iter_->begin()), vals_end_(chunk_iter_->end()) {
            if (val_iter_ == vals_end_) {
                // set is empty
                chunk_iter_ = chunks_end_;
            }
        }
        iterator& operator=(const iterator&) = default;

        iterator& operator++() {
            // assumes that all chunks are nonempty
            ++val_iter_;
            if (val_iter_ == vals_end_) {
                ++chunk_iter_;
                if (chunk_iter_ != chunks_end_) {
                    val_iter_ = chunk_iter_->begin();
                    vals_end_ = chunk_iter_->end();
                } else {
                    val_iter_.set_ = nullptr;
                }
            }
            return *this;
        }
        value_type operator*() const {
            return *val_iter_;
        }
        bool operator==(const iterator& iter) {
            return chunk_iter_ == iter.chunk_iter_ &&
                   ((chunk_iter_ == chunks_end_ ||
                     iter.chunk_iter_ == iter.chunks_end_) ||
                    val_iter_ == iter.val_iter_);
        }
        bool operator!=(const iterator& iter) {
            return !operator==(iter);
        }
    };

    ChunkedIntSet():
        chunks_({ IntSet() }), size_(0) {
    }
    ChunkedIntSet(const ChunkedIntSet&) = default;
    ChunkedIntSet(ChunkedIntSet&&) = default;
    ChunkedIntSet& operator=(const ChunkedIntSet&) = default;
    ChunkedIntSet& operator=(ChunkedIntSet&&) = default;
    ~ChunkedIntSet() = default;

    void push_back(value_type v) {
        IntSet* curr_set = &chunks_.back();
        if (curr_set->capacity() > chunk_size_ &&
            curr_set->space() + value_size_ > curr_set->capacity()) {
            chunks_.push_back(IntSet());
            curr_set = &chunks_.back();
        }
        curr_set->push_back(v);
        ++size_;
    }
    size_t size() const {
        return size_;
    }
    iterator begin() const {
        return iterator(*this);
    }
    iterator end() const {
        iterator iter;
        iter.chunk_iter_ = iter.chunks_end_ = chunks_.end();
        return iter;
    }
    size_t space() const {
        size_t t = 0;
        for (const IntSet& chunk : chunks_) {
            t += chunk.space();
        }
        return t;
    }
    size_t capacity() const {
        size_t t = 0;
        for (const IntSet& chunk : chunks_) {
            t += chunk.capacity();
        }
        return t;
    }
    void swap(ChunkedIntSet& set) {
        chunks_.swap(set.chunks_);
        std::swap(size_, set.size_);
    }

    // Iterator that behaves like a wick, destroying chunks behind it.
    // This frees up memory as the set is traversed.
    struct wicked_iterator {
        ChunkedIntSet* set_;
        list <IntSet>::iterator chunk_iter_, chunks_end_;
        IntSet::iterator val_iter_, vals_end_;

        wicked_iterator() = default;
        wicked_iterator(ChunkedIntSet& set):
            set_(&set),
            chunk_iter_(set.chunks_.begin()), chunks_end_(set.chunks_.end()),
            val_iter_(chunk_iter_->begin()), vals_end_(chunk_iter_->end()) {
            if (val_iter_ == vals_end_) {
                // set is empty
                chunk_iter_ = chunks_end_;
            }
        }
        wicked_iterator& operator=(const wicked_iterator&) = default;

        wicked_iterator& operator++() {
            ++val_iter_;
            if (val_iter_ == vals_end_) {
                set_->size_ -= chunk_iter_->size();
                chunk_iter_ = set_->chunks_.erase(chunk_iter_);
                if (chunk_iter_ != chunks_end_) {
                    val_iter_ = chunk_iter_->begin();
                    vals_end_ = chunk_iter_->end();
                }
            }
            return *this;
        }
        value_type operator*() const {
            return *val_iter_;
        }
        bool operator==(const wicked_iterator& iter) {
            return set_ == iter.set_ &&
                   chunk_iter_ == iter.chunk_iter_ &&
                   ((chunk_iter_ == chunks_end_ ||
                     iter.chunk_iter_ == iter.chunks_end_) ||
                    val_iter_ == iter.val_iter_);
        }
        bool operator!=(const wicked_iterator& iter) {
            return !operator==(iter);
        }
    };
    
    wicked_iterator wicked_begin() {
        return wicked_iterator(*this);
    }
    wicked_iterator wicked_end() {
        wicked_iterator iter;
        iter.set_ = this;
        iter.chunk_iter_ = iter.chunks_end_ = chunks_.end();
        return iter;
    }
};

void test_IntSet() {
    size_t test_size = 1000000;
    DEBUG("Test: store %zu integers in IntSet\n", test_size);
    vector <unsigned> v;
    for (size_t i = 0; i < test_size; ++i) {
        v.push_back(rand() % 1000000);
    }
    sort(v.begin(), v.end());

    ChunkedIntSet set;
    for (size_t i = 0; i < v.size(); ++i) {
        set.push_back(v[i]);
    }
    size_t i = 0;
    for (ChunkedIntSet::iterator it = set.begin(); it != set.end(); ++it, ++i) {
        assert (*it == v[i]);
    }
    DEBUG("Success. Used %zu bytes to store %zu integers\n",
          set.space(), test_size);
}

/*
 * Algorithm to compute S_5.
 * We first rescale S_4 to the range [0, S_4_denom],
 * which makes all elements and subset sums integer.
 * Then we add one element at a time to a database of
 * known subset sums (and their sizes).
 */
void list_S5(const set <mpq_class>& S_4)
{
    vector <uint64_t> S_4_scaled;
    for (const mpq_class& x : S_4) {
        S_4_scaled.push_back(x.get_num().get_ui() * (S_4_denom / x.get_den().get_ui()));
    }

    ChunkedIntSet subset_sums[S_4_size + 1];
    // We add the subset sum 0 to each size, to ensure that we collect
    // sums for 1-element sets {x}. This is ok because S_4 does
    // contain 0, and 0/sz = 0 for all subset sizes sz.
    for (size_t i = 0; i <= S_4_size; ++i) {
        subset_sums[i].push_back(0);
    }

    // Add each element to the known subset sums.
    for (size_t iter = 0; iter < S_4_size; ++iter) {
        uint64_t x = S_4_scaled[iter];
        if (x == 0) {
            // we already added 0 previously
            continue;
        }

        // This merges subset_sums[sz] + {x} into subset_sums[sz+1]
        for (unsigned sz = iter+1; sz > 0; --sz) {
            ChunkedIntSet new_sums;
            /*
             * We want to merge {x+y | y in subset_sums[sz-1]} and
             * subset_sums[sz] into new_sums. To conserve memory,
             * we use a wicked iterator to burn up subset_sums[sz].
             */
            ChunkedIntSet::iterator ix = subset_sums[sz-1].begin();
            ChunkedIntSet::wicked_iterator i = subset_sums[sz].wicked_begin();
            for (;;) {
                if (i == subset_sums[sz].wicked_end()) {
                    if (ix == subset_sums[sz-1].end()) {
                        break;
                    } else {
                        new_sums.push_back(*ix + x);
                        ++ix;
                    }
                } else if (ix == subset_sums[sz-1].end()) {
                    new_sums.push_back(*i);
                    ++i;
                } else {
                    if (*i < *ix + x) {
                        new_sums.push_back(*i);
                        ++i;
                    } else if (*i > *ix + x) {
                        new_sums.push_back(*ix + x);
                        ++ix;
                    } else {
                        new_sums.push_back(*i);
                        ++i, ++ix;
                    }
                }
            }
            subset_sums[sz].swap(new_sums);
        }

        // stats
        size_t size = 0, mem = 0;
        for (size_t i = 1; i <= iter+1; ++i) {
            size += subset_sums[i].size();
            mem += subset_sums[i].capacity();
        }
        DEBUG("Done iter %zu (elem = %3zu/%3zu), size = %zu, mem = %zu K, subset sizes:",
              iter+1, x / gcd(x, S_4_denom), S_4_denom / gcd(x, S_4_denom),
              size, mem >> 10);
        for (size_t i = 1; i <= iter+1; ++i) {
            DEBUG_MORE(" %zu", subset_sums[i].size());
        }
        DEBUG_MORE("\n\n");
    }
}

/*
 * Calculate all subset sums only.
 * (Answer: 7508566125 unique sums)
 *
 * 7.5e9 is 75% of the theoretical range of 10e9 (S_4_denom * S_4_size).
 * This means that tricks like indexing the subset averages in list_S5
 * by rank are not going to help much.
 */
void subset_sums_S5(const set <mpq_class>& S_4)
{
    vector <uint64_t> S_4_scaled;
    for (const mpq_class& x : S_4) {
        S_4_scaled.push_back(x.get_num().get_ui() * (S_4_denom / x.get_den().get_ui()));
    }

    ChunkedIntSet raw_subset_sums;
    // This ensures that we collect sums for 1-element sets {x}
    raw_subset_sums.push_back(0);
    for (size_t iter = 0; iter < S_4_scaled.size(); ++iter) {
        uint64_t x = S_4_scaled[iter];
        /*
         * Memory-conserving trick. We want to merge the sets
         * raw_subset_sums and {x+y | y in raw_subset_sums} into
         * raw_subset_sums2, without using much more space than
         * needed to store the merged sequence.
         *
         * We use a standard iterator on rss to represent itself,
         * and a wicked iterator on rss to represent rss+x (implicitly).
         * Then we merge the sequences that these iterators represent.
         * Since y+x >= y, the wicked iterator always trails behind
         * the standard iterator, freeing memory chunks behind itself.
         * Thus the excess memory usage is the span of a width-x window
         * over rss (rounded up to a multiple of the chunk size).
         * Since 0<=x<=1 (before S_4_denom scaling) and the subset sums
         * can be much larger than 1, this excess should be a small
         * fraction of the result size.
         */
        ChunkedIntSet raw_subset_sums2;
        ChunkedIntSet::iterator i = raw_subset_sums.begin();
        ChunkedIntSet::wicked_iterator ix = raw_subset_sums.wicked_begin();
        for (;;) {
            if (i == raw_subset_sums.end() &&
                ix == raw_subset_sums.wicked_end()) {
                break;
            } else if (i == raw_subset_sums.end() || *ix + x < *i) {
                raw_subset_sums2.push_back(*ix + x);
                ++ix;
            } else if (ix == raw_subset_sums.wicked_end() || *i < *ix + x) {
                raw_subset_sums2.push_back(*i);
                ++i;
            } else /* if (*i == *ix + x) */ {
                raw_subset_sums2.push_back(*i);
                ++i, ++ix;
            }
        }
        raw_subset_sums.swap(raw_subset_sums2);
        DEBUG("Raw subset sums: iter = %zu (q = %3zu/%3zu), #sums = %zu (%zu bytes)\n",
              iter+1, x / gcd(x, S_4_denom), S_4_denom / gcd(x, S_4_denom),
              raw_subset_sums.size(), raw_subset_sums.space());
    }
}

/*
 * Algorithm to estimate |S_5|. We use two estimation methods.
 *
 * Birthday sampling:
 *
 * We assume that picking a subset of S_4 at random will produce a
 * uniformly random average. (This is of course a complete lie.)
 * So, we generate some random subsets until we find a duplicate
 * average value. Suppose that we needed K subsets; then K^2 is a
 * (very approximate) max-likelihood estimate of the size of S_4.
 * We can get a slightly better estimate by repeating this procedure
 * and taking the median of the results.
 *
 * Of course, the distribution of averages is very far from uniform;
 * hence, our naïve estimate will be lower than the true value.
 * In particular, subsets of size S will tend to be distinct from
 * other subsets when S has few prime factors, and completely
 * disjoint from other sizes if S is a large prime
 * (larger than sqrt |S_4| and any prime in S_4_denom).
 *
 * We can compensate for this a bit by sampling each size S
 * independently and summing the results. Note that this introduces
 * some upward bias due to double-counting.
 *
 * (The code below estimates the total size as 1.1e11.)
 */
uint64_t estimate_a5(const set <mpq_class>& S_4, const unsigned n_samples) {
    vector <uint64_t> S_4_scaled;
    for (const mpq_class& x : S_4) {
        S_4_scaled.push_back(x.get_num().get_ui() * (S_4_denom / x.get_den().get_ui()));
    }

    uint64_t total = 0;
    // Estimates for individual sizes
    vector <uint64_t> est_sizes(S_4.size() + 1);
    for (size_t sz = 1; sz <= S_4.size(); ++sz) {
        vector <uint64_t> BD_samples;
        for (unsigned i = 0; i < n_samples; ++i) {
            // one sample
            set <pair <uint64_t, uint64_t>> vals;
            for (;;) {
                random_shuffle(S_4_scaled.begin(), S_4_scaled.end());
                uint64_t sum = 0;
                for (size_t j = 0; j < sz; ++j) {
                    sum += S_4_scaled[j];
                }
                uint64_t d = gcd(sum, sz);
                pair <uint64_t, uint64_t> avg = { sum / d, sz / d };
                if (vals.find(avg) != vals.end()) {
                    break;
                }
                vals.insert(avg);
            }
            BD_samples.push_back(vals.size() * vals.size());
        }
        sort(BD_samples.begin(), BD_samples.end());
        uint64_t BD_median = BD_samples[BD_samples.size() / 2];
        est_sizes[sz] = BD_median;

        double BD_mean = 0, BD_stddev = 0;
        for (uint64_t sample : BD_samples) {
            BD_mean += sample;
        }
        BD_mean /= BD_samples.size();
        for (uint64_t sample : BD_samples) {
            double x = double(BD_mean) - sample;
            BD_stddev += x*x;
        }
        BD_stddev = sqrt(BD_stddev / (BD_samples.size() - 1));

        DEBUG("Estimate for size-%zu subsets: %" PRIu64 ", mean %.2g, stddev %.2g\n",
              sz, est_sizes[sz], BD_mean, BD_stddev);
        total += est_sizes[sz];
    }

    DEBUG("First-order birthday estimate for total: %" PRIu64 "\n", total);

    return total;
}

int main()
{
    set <mpq_class> S_0 = {0, 1};
    set <mpq_class> S_1 = next_naive(S_0);
    set <mpq_class> S_2 = next_naive(S_1);
    set <mpq_class> S_3 = next_naive(S_2);
    set <mpq_class> S_4 = next_naive(S_3);
    {
        uint64_t check_S_4_denom = 1;
        for (const mpq_class& x : S_4) {
            assert (x.get_den().fits_ulong_p());
            check_S_4_denom = lcm(check_S_4_denom, x.get_den().get_ui());
        }
        assert (check_S_4_denom == S_4_denom);
        assert (S_4.size() == S_4_size);
    }

    //test_IntSet();

    list_S5(S_4);
    return 0;

    srand(time(0));
    estimate_a5(S_4, 100);
}
