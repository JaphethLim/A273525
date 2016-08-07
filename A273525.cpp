/*
 * OEIS A273525: define
 *   S_0 = {0, 1}
 *   S_{n+1} = { sum(s)/size(s) for nonempty s \subseteq S_n }
 *
 * Then a_n = size(S_n).
 * It is easy to see that a_0 = 2, a_1 = 3, a_2 = 5, a_3 = 15, a_4 = 875.
 * This program calculates a_5.
 */

#include <cinttypes>
#include <cmath>
#include <cstdio>
#include <ctime>

#include <mutex>
#include <thread>

#include <algorithm>
#include <list>
#include <queue>
#include <set>
#include <tuple>
#include <vector>

#include <gmpxx.h>

#include <getopt.h>

// TurboPFor includes
#include "bitpack.h"
#include "bitunpack.h"
#include "vp4dc.h"
#include "vp4dd.h"

#ifdef ROCKET
# define assert(...) (void)0
#else
# include <cassert>
#endif

#ifdef __GNUC__
# ifndef likely
#  define likely(x) __builtin_expect(x, 1)
# endif
# ifndef unlikely
#  define unlikely(x) __builtin_expect(x, 0)
# endif
#else
# warning "non GNU compiler; using dummy likely() and unlikely() macros"
# define likely(x) (x)
# define unlikely(x) (x)
#endif

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
 * We use TurboPFor to compress and decompress blocks of integer gaps
 * (P4DSIZE=128 values per block). To accommodate iteration and
 * push_back, sets and iterators have an internal buffer of integers.
 * (NB: this means that iterators are over 1KiB in size.)
 */
struct IntSet {
    typedef uint64_t value_type;

    // FIXME: std::min isn't constexpr??
    static const size_t buffer_size_ = P4DSIZE > 128? 128 : P4DSIZE;
    // Conservative guess used by push_back and ChunkedIntSet
    // Note that log C(2^64, 128) < 934 bytes so we should be safe
    static const size_t enc_buffer_size_ = buffer_size_ * 8;
    // Block size for 2-pass prefix sum
    static const size_t prefix_sum_block_ = 8;

    // stream_ only contains full buffer_size_ blocks, partial blocks
    // are always left in buffer_
    vector <uint8_t> stream_;
    size_t stream_size_; // number of values in stream
    array <value_type, buffer_size_> buffer_;
    size_t pending_; // number of values in buffer
    value_type max_; // largest value in stream_, else 0

    struct iterator {
        const IntSet* set_;
        size_t elem_pos_, stream_pos_, buffer_pos_;
        array <value_type, buffer_size_> buffer_;

        iterator():
            set_(nullptr) {
        }
        iterator(const iterator&) = default;
        iterator& operator=(const iterator&) = default;
        iterator(const IntSet& set):
            set_(&set), elem_pos_(0), stream_pos_(0) {
            if (elem_pos_ < set.stream_size_) {
                stream_pos_ =
                    p4ddec64(const_cast <uint8_t*> (&set.stream_[stream_pos_]),
                             buffer_size_, &buffer_[0])
                     - &set.stream_[0];
                prefix_sum_(0);
                buffer_pos_ = 0;
            }
        }

        iterator& operator++() {
            if (elem_pos_ < set_->stream_size_) {
                ++buffer_pos_;
                ++elem_pos_;
                if (buffer_pos_ == buffer_size_ && elem_pos_ < set_->stream_size_) {
                    uint64_t prev = buffer_.back();
                    stream_pos_ =
                        p4ddec64(const_cast <uint8_t*> (&set_->stream_[stream_pos_]),
                                 buffer_size_, &buffer_[0])
                         - &set_->stream_[0];
                    prefix_sum_(prev);
                    buffer_pos_ = 0;
                }
            } else {
                ++elem_pos_;
            }
            return *this;
        }
        value_type operator*() const {
            if (elem_pos_ < set_->stream_size_) {
                return buffer_[buffer_pos_];
            } else {
                return set_->buffer_[elem_pos_ - set_->stream_size_];
            }
        }
        bool operator==(const iterator& it) const {
            return set_ == it.set_ && elem_pos_ == it.elem_pos_;
        }
        bool operator!=(const iterator& it) const {
            return !operator==(it);
        }

        void prefix_sum_(value_type initial) {
            buffer_[0] += initial;
            if (true) {
                for (size_t i = 1; i < buffer_size_; ++i) {
                    buffer_[i] += buffer_[i - 1];
                }
            } else {
                for (size_t i = 1; i < prefix_sum_block_ && i < buffer_size_; ++i) {
                    buffer_[i] += buffer_[i - 1];
                }
                for (size_t b = prefix_sum_block_; b < buffer_size_; b += prefix_sum_block_) {
                    for (size_t i = 1; i < prefix_sum_block_ && i < buffer_size_ - b; ++i) {
                        buffer_[b + i] += buffer_[b + i - 1];
                    }
                }
                for (size_t b = prefix_sum_block_; b < buffer_size_; b += prefix_sum_block_) {
                    for (size_t i = 0; i < prefix_sum_block_ && i < buffer_size_ - b; ++i) {
                        buffer_[b + i] += buffer_[b - 1];
                    }
                }
            }
        }
    };

    IntSet():
        stream_size_(0), pending_(0), max_(0) {
    }
    IntSet(const IntSet& set) = default;
    IntSet(IntSet&& set) = default;
    IntSet& operator=(const IntSet&) = default;
    IntSet& operator=(IntSet&&) = default;
    ~IntSet() = default;

    void push_back(value_type v) {
        buffer_[pending_++] = v;
        if (pending_ == buffer_size_) {
            // Do delta encoding out-of-place for better (?) parallelism
            array <value_type, buffer_size_> buffer_gaps;
            buffer_gaps[0] = buffer_[0] - max_;
            for (size_t i = 1; i < buffer_size_; ++i) {
                buffer_gaps[i] = buffer_[i] - buffer_[i-1];
            }
            // Be extra careful here
            uint8_t buf[enc_buffer_size_ + 100];
            uint8_t* buf_end = p4denc64(&buffer_gaps[0], buffer_size_, buf);
            // Check our original bound
            assert (buf_end - buf < ssize_t(enc_buffer_size_));
            stream_.insert(stream_.end(), buf, buf_end);
            stream_size_ += pending_;
            pending_ = 0;
            max_ = buffer_.back();
        }
    }
    size_t size() const {
        return stream_size_ + pending_;
    }
    iterator begin() const {
        return iterator(*this);
    }
    iterator end() const {
        iterator it;
        it.set_ = this;
        it.elem_pos_ = size();
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
        std::swap(stream_size_, set.stream_size_);
        buffer_.swap(set.buffer_);
        std::swap(pending_, set.pending_);
        std::swap(max_, set.max_);
    }
    void clear() {
        stream_.clear();
        stream_size_ = pending_ = max_ = 0;
    }
};

/*
 * Chunked version of IntSet. Avoids memory (re-)allocation issues
 * for very large sets.
 */
struct ChunkedIntSet {
    typedef IntSet::value_type value_type;

    list <IntSet> chunks_;
    size_t size_;

    /* We fill up to chunk_size_ - buffer_size_enc_ bytes of each chunk
     * before we decide to move to a new chunk.
     * This is to avoid having to deal with overrunning the space in
     * each chunk when inserting.
     *
     * Note that the space usage of the list_S5 decode-reverse code can
     * be a large (64/compressed size) multiple of the chunk size.
     * For a (quite typical) compressed size of 1 bit/entry, we get
     *   chunk_size_ * 2 (vector growth factor) * (64 / 1) = 16MiB */
    static const size_t chunk_size_ = 1 << 17;
    static const size_t value_size_ = 9;

    struct iterator {
        list <IntSet>::const_iterator chunk_iter_, chunks_end_;
        IntSet::iterator val_iter_, vals_end_;

        iterator() = default;
        iterator(const ChunkedIntSet& set):
            chunk_iter_(set.chunks_.begin()), chunks_end_(set.chunks_.end()) {
            if (chunk_iter_ != chunks_end_) {
                val_iter_ = chunk_iter_->begin();
                vals_end_ = chunk_iter_->end();
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
        chunks_(), size_(0) {
    }
    ChunkedIntSet(const ChunkedIntSet&) = default;
    ChunkedIntSet(ChunkedIntSet&&) = default;
    ChunkedIntSet& operator=(const ChunkedIntSet&) = default;
    ChunkedIntSet& operator=(ChunkedIntSet&&) = default;
    ~ChunkedIntSet() = default;

    void push_back(value_type v) {
        if (unlikely(chunks_.empty())) {
            IntSet new_chunk;
            new_chunk.push_back(v);
            chunks_.emplace_back(new_chunk);
        } else {
            IntSet& curr_set = chunks_.back();
            if (unlikely(curr_set.space() + IntSet::enc_buffer_size_ > curr_set.capacity() &&
                         curr_set.capacity() > chunk_size_)) {
                IntSet new_chunk;
                new_chunk.push_back(v);
                chunks_.emplace_back(new_chunk);
            } else {
                curr_set.push_back(v);
            }
        }
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
    void clear() {
        chunks_.clear();
        size_ = 0;
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
            chunk_iter_(set.chunks_.begin()), chunks_end_(set.chunks_.end()) {
            if (chunk_iter_ != chunks_end_) {
                val_iter_ = chunk_iter_->begin();
                vals_end_ = chunk_iter_->end();
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
    int seed = time(0);
    DEBUG("Random seed: %d\n", seed);
    srand(seed);

    auto do_test = [&](const char* noun, vector <uint64_t> v) {
        DEBUG("Test: store %zu %s in IntSet\n", v.size(), noun);
        sort(v.begin(), v.end());
        ChunkedIntSet set;
        for (size_t i = 0; i < v.size(); ++i) {
            set.push_back(v[i]);
        }
        size_t i;
        DEBUG("  Testing iterator...\n");
        i = 0;
        for (ChunkedIntSet::iterator it = set.begin(); it != set.end(); ++it, ++i) {
            assert (*it == v[i]);
        }
        DEBUG("  success. Used %zu bytes to store %zu %s\n",
              set.space(), v.size(), noun);

        assert (i == v.size());
        DEBUG("  Testing wicked_iterator...\n");
        i = 0;
        for (ChunkedIntSet::wicked_iterator it = set.wicked_begin();
             it != set.wicked_end(); ++it, ++i) {
            assert (*it == v[i]);
        }
        assert (set.size() == 0);
        assert (i == v.size());
        DEBUG("  success.\n");
    };

    size_t test_size = 1000000;
    {
        vector <uint64_t> v;
        for (size_t i = 0; i < test_size; ++i) {
            v.push_back(rand() % test_size);
        }
        do_test("small integers", v);
    }
    {
        vector <uint64_t> v;
        for (size_t i = 0; i < test_size; ++i) {
            v.push_back(rand());
        }
        do_test("medium integers", v);
    }
    {
        vector <uint64_t> v;
        for (size_t i = 0; i < test_size; ++i) {
            v.push_back(uint64_t(rand()) * uint64_t(rand()));
        }
        do_test("large integers", v);
    }
}

/*
 * Algorithm to compute S_5.
 * We first rescale S_4 to the range [0, S_4_denom],
 * which makes all elements and subset sums integer.
 * Then we add one element at a time to a database of
 * known subset sums (and their sizes).
 * Finally, we remove duplicates from the averages.
 */
static const unsigned num_threads = 4;
uint64_t list_S5(const set <mpq_class>& S_4)
{
    // recalculate, for testing with sets other than S_4 itself
    uint64_t S_4_denom = 1;
    for (const mpq_class& x : S_4) {
        assert (x.get_den().fits_ulong_p());
        S_4_denom = lcm(S_4_denom, x.get_den().get_ui());
    }
    vector <uint64_t> S_4_scaled;
    for (const mpq_class& x : S_4) {
        S_4_scaled.push_back(x.get_num().get_ui() * (S_4_denom / x.get_den().get_ui()));
    }

    vector <ChunkedIntSet> subset_sums(S_4.size() + 1);
    // Ensure that we collect sums for 1-element sets {x}.
    subset_sums[0].push_back(0);

    // Add each element to the known subset sums.
    for (size_t iter = 1; iter <= S_4.size(); ++iter) {
        uint64_t x = S_4_scaled[iter-1];

        // Note that by symmetry, subset_sums[sz] are the same as
        // sum(S_4) - subset_sums[iter - sz], so we only need to keep track
        // of sizes up to iter/2.
        size_t max_sz = iter / 2;
        vector <ChunkedIntSet> new_subset_sums(max_sz + 1);
        // We farm out the per-sz merges to multiple threads.
        mutex pool_mutex;
        vector <size_t> merge_jobs;
        for (size_t sz = 1; sz <= max_sz; ++sz) {
            merge_jobs.push_back(sz);
        }

        // Each subset_sums[i] is used in 1-2 merges, and we'd like to
        // delete it after they are finished.
        vector <unsigned> pending_merges(max_sz + 1);
        pending_merges[0] = 99; // only 1-2, but we don't want to free it
        for (size_t i = 1; i + 1 < max_sz; ++i) {
            pending_merges[i] = 2;
        }
        // the last set is only used in one merge
        --pending_merges[max_sz];

        auto worker = [&]() {
            for (;;) {
                size_t sz;
                { lock_guard <mutex> lock(pool_mutex);
                    if (merge_jobs.empty()) {
                        return;
                    } else {
                        sz = merge_jobs.back();
                        merge_jobs.pop_back();
                    }
                }
                // Merge {x+y | y in subset_sums[sz-1]} and subset_sums[sz]
                // into new_subset_sums[sz].
                ChunkedIntSet::iterator ix = subset_sums[sz-1].begin();
                ChunkedIntSet mid_rev;
                size_t right_merge = sz;
                if (sz == max_sz) {
                    if (iter % 2 == 0) {
                        // If iter is even, subset_sums[max_sz] is empty because we
                        // didn't compute it until now. Fortunately, by symmetry
                        // it is equal to subset_sums[max_sz - 1].
                        right_merge = sz - 1;
                    }
                    // We also need to negate the subsets, which involves
                    // reversing the sum sequence
                    uint64_t total_sum = 0;
                    for (size_t i = 0; i + 1 < iter; ++i) {
                        total_sum += S_4_scaled[i];
                    }
                    list <IntSet>::const_reverse_iterator ci;
                    const ChunkedIntSet& shadow = subset_sums[right_merge];
                    for (ci = shadow.chunks_.rbegin(); ci != shadow.chunks_.rend(); ++ci) {
                        vector <uint64_t> chunk(ci->size());
                        size_t i = ci->size();
                        for (uint64_t nx: *ci) {
                            chunk[--i] = total_sum - nx;
                        }
                        for (uint64_t x: chunk) {
                            mid_rev.push_back(x);
                        }
                    }
                }
                const ChunkedIntSet& right_set =
                    sz == max_sz? mid_rev : subset_sums[right_merge];
                ChunkedIntSet::iterator i = right_set.begin();
                ChunkedIntSet new_sums;
                for (;;) {
                    if (unlikely(i == right_set.end())) {
                        if (unlikely(ix == subset_sums[sz-1].end())) {
                            break;
                        } else {
                            new_sums.push_back(*ix + x);
                            ++ix;
                        }
                    } else if (unlikely(ix == subset_sums[sz-1].end())) {
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
                // Done
                { lock_guard <mutex> lock(pool_mutex);
                  new_subset_sums[sz].swap(new_sums);
                  if (--pending_merges[sz-1] == 0) {
                      subset_sums[sz-1].clear();
                  }
                  if (--pending_merges[right_merge] == 0) {
                      subset_sums[right_merge].clear();
                  }
                }
            }
        };

        vector <thread> worker_pool;
        for (size_t i = 0; i < num_threads; ++i) {
            worker_pool.emplace_back(thread(worker));
        }
        for (thread& worker : worker_pool) {
            worker.join();
        }
        for (size_t sz = 1; sz <= max_sz; ++sz) {
            subset_sums[sz].swap(new_subset_sums[sz]);
        }

        // Print stats
        size_t size = 0, mem = 0;
        for (size_t i = 1; i < subset_sums.size(); ++i) {
            size += subset_sums[i].size();
            mem += subset_sums[i].capacity();
        }
        DEBUG("Done iter %zu (elem = %3zu/%3zu), size = %zu, mem = %zu K, subset sizes:",
              iter, x / gcd(x, S_4_denom), S_4_denom / gcd(x, S_4_denom),
              size, mem >> 10);
        for (size_t i = 1; i <= max_sz; ++i) {
            DEBUG_MORE(" %zu", subset_sums[i].size());
        }
        DEBUG_MORE("\n");

#ifndef ROCKET
        // Print gap distribution stats every few iterations.
        // This involves a full scan of the state
        if (iter % 5 == 0) {
            DEBUG("Gap distribution stats:");
            array <size_t, 65> gaps = {};
            for (size_t sz = 1; sz <= max_sz; ++sz) {
                uint64_t prev = 0;
                for (uint64_t x: subset_sums[sz]) {
                    if (prev) {
                        size_t bits = 0;
                        for (; bits < 64 && (x - prev) >> bits; ++bits);
                        ++gaps[bits];
                    }
                    prev = x;
                }
            }
            for (size_t bits = 0; bits < gaps.size(); ++bits) {
                if (gaps[bits]) {
                    DEBUG_MORE(" 2^%zu=%zu", bits, gaps[bits]);
                }
            }
            DEBUG_MORE("\n");
        }
#endif

        if (false) {
            // Print everything
            DEBUG("Subset sums:\n");
            for (size_t sz = 1; sz < subset_sums.size(); ++sz) {
                if (subset_sums[sz].size() == 0) continue;
                DEBUG("  Size %zu:", sz);
                for (uint64_t x: subset_sums[sz]) {
                    uint64_t d = gcd(x, sz * S_4_denom);
                    DEBUG_MORE(" %zu/%zu", x / d, sz * S_4_denom / d);
                }
                DEBUG_MORE("\n");
            }
        }

        DEBUG("\n");
    }

    /*
     * Compute and collect the subset averages.
     * Each sequence subset_sums[sz] = a1/sz, a2/sz...
     * is already sorted; we reduce them to lowest terms i.e.
     * a_i/sz = b_i/d_i, then group them into subsequences for
     * each d_i. Note that each subsequence is still sorted.
     */
    vector <list <ChunkedIntSet>> denom_groups(subset_sums.size());
    /*
     * Merge and count (and then delete) sequences for each denominator.
     * This is interleaved with the above
     */
    size_t S_5_size = 0;

    {
        /* Worker threads do double duty here: they split the subset
         * averages according to their true (reduced) denominators;
         * they also merge and count subset averages for a given denom
         * when all the averages have been collected for that denom. */
        mutex pool_mutex;
        // Each subset_sums[sz] is also used to generate the symmetric
        // subset_sums[S_4_size - sz]. We'd like to free it as soon as
        // both are done.
        vector <unsigned> pending_splits(S_4.size() + 1, 2);
        if (S_4.size() % 2 == 0) {
            pending_splits[S_4.size() / 2] = 1;
        }

        /* We schedule pairs of sizes (sz, S_4_size - sz) together so
         * that the underlying subset_sums[sz] can be freed right away.
         *
         * Since the collection phase expands the [S_4_size-sz] values
         * and creates multiple subsets for each denominator, it is
         * the phase that consumes the most memory. Hence, we do a
         * little optimisation to find a schedule that reduces the
         * peak memory usage. */
        vector <size_t> extract_jobs;
        {
            /*
             * We model the memory cost like this:
             *
             * When collecting a given subset_sums[sz], we assume that
             * the number of resulting averages with denominator d is
             *   avg.size ≈ subset_sums[sz].size * φ(d)/sz
             * (φ is the totient function), i.e. the sums are “well
             * distributed”. The memory cost is estimated as
             *   avg.size * log_2(subset_sums[sz].size / avg.size)
             * to account for the compressed IntSet encoding.
             *
             * Finally, we assume that the schedule is executed
             * by a single thread in sequence. Then we just swap
             * some entries in the schedule to (locally) optimise
             * the total memory usage.
             */
            vector <pair <size_t, size_t>> extract_pairs;
            for (size_t i = 0; i <= S_4.size() - i; ++i) {
                extract_pairs.push_back(make_pair(i, S_4.size() - i));
            }

            vector <size_t> phi(S_4.size() + 1);
            for (size_t n = 1; n <= S_4.size(); ++n) {
                for (size_t d = 1; d <= n; ++d) {
                    if (gcd(n, d) == 1) {
                        ++phi[n];
                    }
                }
            }
            vector <vector <size_t>> divisors_of(S_4.size() + 1);
            for (size_t n = 1; n <= S_4.size(); ++n) {
                for (size_t d = 1; d <= n; ++d) {
                    if (n % d == 0) {
                        divisors_of[n].push_back(d);
                    }
                }
            }
            vector <size_t> split_deps0(S_4.size() + 1);
            for (size_t n = 1; n <= S_4.size(); ++n) {
                split_deps0[n] = S_4.size() / n;
            }
            auto memory_cost = [&]() -> pair <size_t, size_t> {
                size_t current_cost = 0;
                for (const ChunkedIntSet& set: subset_sums) {
                    current_cost += set.capacity();
                }
                size_t peak_cost = current_cost, total_cost = 0;
                vector <size_t> denom_costs(S_4.size() + 1);
                vector <size_t> split_deps = split_deps0;
                vector <bool> has_merged(S_4.size() + 1);
                auto sim_split = [&](size_t sz) {
                    for (size_t d: divisors_of[sz]) {
                        size_t subgroup_size = subset_sums[sz].size() * phi[d] / sz;
                        size_t subgroup_mem = 0;
                        if (subgroup_size) {
                            subgroup_mem = subgroup_size *
                              (1 + log(double(subset_sums[sz].size()) / subgroup_size) / log(2)) / 8;
                        }
                        denom_costs[d] += subgroup_mem;
                        current_cost += subgroup_mem;
                        --split_deps[d];
                    }
                    current_cost -= subset_sums[sz].capacity();
                };
                auto sim_merge = [&](size_t last_split) {
                    for (size_t denom: divisors_of[last_split]) {
                        if (!has_merged[denom] && split_deps[denom] == 0) {
                            current_cost -= denom_costs[denom];
                            has_merged[denom] = true;
                        }
                    }
                };
                for (size_t i = 0; i < extract_pairs.size(); ++i) {
                    sim_split(extract_pairs[i].first);
                    peak_cost = max(current_cost, peak_cost);
                    total_cost += current_cost;
                    sim_merge(i);
                    if (extract_pairs[i].second != extract_pairs[i].first) {
                        sim_split(extract_pairs[i].second);
                        peak_cost = max(current_cost, peak_cost);
                        total_cost += current_cost;
                        sim_merge(i);
                    }
                }
                return make_pair(peak_cost, total_cost);
            };
            DEBUG("Optimising collect schedule...\n");
            pair <size_t, size_t> cost = memory_cost();
            // sort-of greedy optimisation
            for (size_t tries = 1; tries < S_4.size(); ++tries) {
                DEBUG("  pass %zu\n", tries);
                bool changed = false;
                for (size_t i = 0; i < extract_pairs.size(); ++i) {
                    size_t best_swap = i;
                    pair <size_t, size_t> best_cost = cost;
                    for (size_t j = i + 1; j < extract_pairs.size(); ++j) {
                        std::swap(extract_pairs[i], extract_pairs[j]);
                        pair <size_t, size_t> new_cost = memory_cost();
                        if (new_cost < best_cost) {
                            best_cost = new_cost;
                            best_swap = j;
                        }
                        std::swap(extract_pairs[i], extract_pairs[j]);
                    }
                    if (best_swap != i) {
                        changed = true;
                        std::swap(extract_pairs[i], extract_pairs[best_swap]);
                        cost = best_cost;
                    }
                }
                if (!changed) {
                    break;
                }
            }

            for (pair <size_t, size_t> p: extract_pairs) {
                if (p.first != 0) {
                    extract_jobs.push_back(p.first);
                }
                if (p.second != 0 && p.second != p.first) {
                    extract_jobs.push_back(p.second);
                }
            }
            DEBUG("Collect schedule, estimated cost=%zu:", cost.first);
            for (size_t sz: extract_jobs) {
                DEBUG_MORE(" %zu", sz);
            }
            DEBUG_MORE("\n");
            // Our workers take jobs back-to-front
            reverse(extract_jobs.begin(), extract_jobs.end());
        }

        // This is used to keep track of which denoms have completely
        // finished, so we can merge and count them sooner
        vector <bool> extract_done(S_4.size() + 1);

        auto larger_group = [&](const list <ChunkedIntSet>::iterator& i1,
                                const list <ChunkedIntSet>::iterator& i2) {
            return i1->size() > i2->size();
        };
        vector <bool> pending_merges(S_4.size() + 1, true);

        auto worker = [&]() {
            for (;;) {
                bool is_merge_job = false;
                size_t job_num;
                {   lock_guard <mutex> lock(pool_mutex);
                    // Find pending denoms that we can merge now.
                    // Every denom eventually becomes eligible once its
                    // multiples have been collected by other jobs, so
                    // this algorithm is complete.
                    for (job_num = 1; job_num <= S_4.size(); ++job_num) {
                        if (!pending_merges[job_num]) continue;
                        bool can_merge = true;
                        for (size_t mul = 1; job_num * mul <= S_4.size(); ++mul) {
                            if (!extract_done[job_num * mul]) {
                                can_merge = false;
                            }
                        }
                        if (can_merge) {
                            is_merge_job = true;
                            pending_merges[job_num] = false;
                            break;
                        }
                    }

                    if (!is_merge_job) {
                        if (extract_jobs.empty()) {
                            return;
                        }
                        job_num = extract_jobs.back();
                        extract_jobs.pop_back();
                    }
                }

                if (is_merge_job) {
                    // Merge averages for denom
                    size_t denom = job_num;
                    // The subsequences have varying sizes; we use a
                    // priority_queue to merge the smallest pair first.
                    priority_queue <list <ChunkedIntSet>::iterator,
                                    vector <list <ChunkedIntSet>::iterator>,
                                    decltype(larger_group)>
                        merge_queue(larger_group);
                    for (list <ChunkedIntSet>::iterator i = denom_groups[denom].begin();
                         i != denom_groups[denom].end(); ++i) {
                        merge_queue.push(i);
                    }
                    while (merge_queue.size() > 1) {
                        list <ChunkedIntSet>::iterator group1 = merge_queue.top();
                        merge_queue.pop();
                        list <ChunkedIntSet>::iterator group2 = merge_queue.top();
                        merge_queue.pop();
                        // Merge group1 and group2 into a new set, then store it in group1
                        ChunkedIntSet merged_group;
                        ChunkedIntSet::wicked_iterator i1 = group1->wicked_begin(),
                        i2 = group2->wicked_begin();
                        for (;;) {
                            if (unlikely(i1 == group1->wicked_end())) {
                                if (unlikely(i2 == group2->wicked_end())) {
                                    break;
                                } else {
                                    merged_group.push_back(*i2);
                                    ++i2;
                                }
                            } else if (unlikely(i2 == group2->wicked_end())) {
                                merged_group.push_back(*i1);
                                ++i1;
                            } else if (*i1 < *i2) {
                                merged_group.push_back(*i1);
                                ++i1;
                            } else if (*i2 < *i1) {
                                merged_group.push_back(*i2);
                                ++i2;
                            } else {
                                merged_group.push_back(*i1);
                                ++i1, ++i2;
                            }
                        }
                        group1->swap(merged_group);
                        // *group2 is now empty. denom_group[denom] is a list
                        // so we can safely erase group2
                        denom_groups[denom].erase(group2);
                        // Continue merging
                        merge_queue.push(group1);
                    }
                    assert (denom_groups[denom].size() <= 1);

                    {   lock_guard <mutex> lock(pool_mutex);
                        size_t denom_count = 0, mem = 0;
                        if (!denom_groups[denom].empty()) {
                            denom_count += denom_groups[denom].begin()->size();
                            mem += denom_groups[denom].begin()->capacity();
                        }
                        DEBUG("Merged denominator %zu: %zu elems, mem = %zu K\n",
                              denom, denom_count, mem / 1024);

                        if (false) {
                            // Print everything
                            if (!denom_groups[denom].empty()) {
                                DEBUG("Elems:");
                                for (uint64_t x: *denom_groups[denom].begin()) {
                                    uint64_t d = gcd(x, denom * S_4_denom);
                                    DEBUG_MORE(" %zu/%zu", x / d, denom * S_4_denom / d);
                                }
                                DEBUG_MORE("\n");
                            }
                        }
                        S_5_size += denom_count;
                        // We can now free the data for this denom
                        denom_groups[denom].clear();
                    }
                } else {
                    // Collect averages for subsets of given size
                    size_t sz = job_num;
                    vector <ChunkedIntSet> denom_subgroups(denom_groups.size());
                    if (sz <= S_4.size() / 2) {
                        // Split subset_sums by reduced denominators
                        for (ChunkedIntSet::iterator i = subset_sums[sz].begin();
                             i != subset_sums[sz].end(); ++i) {
                            uint64_t x = *i;
                            uint64_t d = gcd(x, sz);
                            denom_subgroups[sz / d].push_back(x / d);
                        }
                    } else {
                        // We skipped subset_sums[sz] for S_4_size/2 < sz <= S_4_size
                        // due to symmetry. Now we need to go back and generate them.
                        uint64_t S_4_sum = 0;
                        for (uint64_t x: S_4_scaled) {
                            S_4_sum += x;
                        }
                        // The values of subset_sum[sz] would be
                        // S_4_sum - subset_sum[S_4_size - sz], but this list
                        // is in reverse order. We fix this simplistically
                        // by fully decoding each chunk and reversing it.
                        // FIXME: this bypasses the ChunkedIntSet interface
                        list <IntSet>::const_reverse_iterator ci;
                        const ChunkedIntSet& shadow = subset_sums[S_4.size() - sz];
                        // We can walk the chunks in reverse without difficulty.
                        for (ci = shadow.chunks_.rbegin(); ci != shadow.chunks_.rend(); ++ci) {
                            vector <uint64_t> chunk(ci->size());
                            size_t i = ci->size() - 1;
                            for (uint64_t nx: *ci) {
                                chunk[i--] = S_4_sum - nx;
                            }
                            // Process the reversed chunk
                            for (uint64_t x: chunk) {
                                uint64_t d = gcd(x, sz);
                                denom_subgroups[sz / d].push_back(x / d);
                            }
                        }
                    }

                    // Return the results
                    {   lock_guard <mutex> lock(pool_mutex);
                        size_t mem = 0;
                        for (ChunkedIntSet& subgroup: denom_subgroups) {
                            mem += subgroup.capacity();
                        }
                        DEBUG("Collected results for size %zu, mem = %zu K, sizes:",
                              sz, mem / 1024);
                        for (size_t i = 0; i < denom_subgroups.size(); ++i) {
                            if (denom_subgroups[i].size()) {
                                DEBUG_MORE(" %zu=%zu", i, denom_subgroups[i].size());
                                denom_groups[i].emplace_back(move(denom_subgroups[i]));
                            }
                        }
                        DEBUG_MORE("\n");

                        size_t source_sz = sz;
                        if (S_4.size() / 2 < sz) {
                            source_sz = S_4.size() - sz;
                        }
                        if (--pending_splits[source_sz] == 0) {
                            subset_sums[source_sz].clear();
                        }

                        extract_done[sz] = true;
                    }
                }
            }
        };

        vector <thread> worker_pool;
        for (size_t i = 0; i < num_threads; ++i) {
            worker_pool.emplace_back(thread(worker));
        }
        for (thread& worker : worker_pool) {
            worker.join();
        }
        subset_sums.clear();

        // We should have merged everything by now
        for (size_t i = 1; i <= S_4.size(); ++i) {
            assert (!pending_merges[i]);
        }
    }
    DEBUG("\n");

    // FIXME: we only return the size; we don't bother returning the elements
    // as promised in the header comment
    return S_5_size;
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

int main(int argc, char** argv)
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

    const char* usage =
        "Usage: %1$s\n"
        "       %1$s -t [intset|dryrun_s4|dryrun_s5]\n";

    int opt;
    while ((opt = getopt(argc, argv, "ht:")) != -1) {
        switch (opt) {
        case 'h':
            printf(usage, argv[0]);
            return 0;
        case 't':
            if (!strcmp(optarg, "intset")) {
                test_IntSet();
                return 0;
            } else if (!strcmp(optarg, "dryrun_s4")) {
                // We expect that the list_S5 algorithm also works
                // when used to calculate S_4.
                size_t size = list_S5(S_3);
                if (size == S_4_size) {
                    printf("S_4 test passed.\n");
                    return 0;
                } else {
                    printf("S_4 test failed: expected %zu, got %zu\n",
                           S_4_size, size);
                    return 1;
                }
            } else if (!strcmp(optarg, "dryrun_s5")) {
                // Calculate over the first 125 elements of S_4.
                set <mpq_class> S_4_125;
                size_t i = 0;
                for (mpq_class x: S_4) {
                    S_4_125.insert(x);
                    if (++i == 125) break;
                }
                size_t size = list_S5(S_4_125);
                const size_t expected = 33947876;
                if (size == expected) {
                    printf("S_5/125 test passed.\n");
                    return 0;
                } else {
                    printf("S_5/125 test failed: expected %zu, got %zu\n",
                           expected, size);
                    return 1;
                }
            } else {
                fprintf(stderr, "Error: no such test: %s\n", optarg);
                return 1;
            }
            break;
        default:
            fprintf(stderr, usage, argv[0]);
            return 1;
        }
    }

    // default action
    printf("|S_5| = %zu\n", list_S5(S_4));
}
