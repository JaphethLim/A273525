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
#include <tuple>
#include <thread>
#include <mutex>
#include <vector>
#include <set>
#include <list>
#include <queue>
#include <gmpxx.h>
#include <getopt.h>

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
            for (; sz < 64 && d >= value_type(1) << sz; sz += 8);
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
    void clear() {
        stream_.clear();
        size_ = 0;
        max_ = 0;
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
    // 512K — gcc's resize policy typically rounds up to 1M
    static const size_t chunk_size_ = 1 << 19;
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

        vector <ChunkedIntSet> new_subset_sums(iter + 1);
        // We farm out the per-sz merges to multiple threads.
        mutex pool_mutex;
        vector <size_t> merge_jobs;
        for (size_t sz = 1; sz <= iter; ++sz) {
            merge_jobs.push_back(sz);
        }

        // Each subset_sums[i] is used in two merges, and we'd like to
        // delete it after both are finished.
        vector <bool> lower_merged(subset_sums.size()), upper_merged(subset_sums.size());
        // Except for subset_sum[iter], which is only merged once.
        // (So is subset_sum[0], but we never touch it.)
        lower_merged[iter] = true;

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
                ChunkedIntSet::iterator i = subset_sums[sz].begin();
                ChunkedIntSet new_sums;
                for (;;) {
                    if (i == subset_sums[sz].end()) {
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
                // Done
                { lock_guard <mutex> lock(pool_mutex);
                  new_subset_sums[sz].swap(new_sums);
                  lower_merged[sz-1] = upper_merged[sz] = true;
                  if (lower_merged[sz-1] && upper_merged[sz-1]) {
                      subset_sums[sz-1].clear();
                  }
                  if (lower_merged[sz] && upper_merged[sz]) {
                      subset_sums[sz].clear();
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
        for (size_t sz = 1; sz <= iter; ++sz) {
            subset_sums[sz].swap(new_subset_sums[sz]);
        }

        // Print stats
        size_t size = 0, mem = 0;
        for (size_t i = 1; i <= iter; ++i) {
            size += subset_sums[i].size();
            mem += subset_sums[i].capacity();
        }
        DEBUG("Done iter %zu (elem = %3zu/%3zu), size = %zu, mem = %zu K, subset sizes:",
              iter, x / gcd(x, S_4_denom), S_4_denom / gcd(x, S_4_denom),
              size, mem >> 10);
        for (size_t i = 1; i <= iter; ++i) {
            DEBUG_MORE(" %zu", subset_sums[i].size());
        }
        DEBUG_MORE("\n");

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
    {
        // We farm out the extraction of subsequences to threads.
        mutex pool_mutex;
        vector <size_t> extract_jobs;
        for (size_t i = 1; i < subset_sums.size(); ++i) {
            extract_jobs.push_back(i);
        }
        auto worker = [&]() {
            for (;;) {
                size_t sz;
                {   lock_guard <mutex> lock(pool_mutex);
                    if (extract_jobs.empty()) {
                        return;
                    }
                    sz = extract_jobs.back();
                    extract_jobs.pop_back();
                }
                vector <ChunkedIntSet> denom_subgroups(denom_groups.size());
                // Wicked iterator reallocates memory to the new subsequences
                // (actually, they will use slightly more memory due to
                // larger gap sizes and chunk fragmentation).
                for (ChunkedIntSet::wicked_iterator i = subset_sums[sz].wicked_begin();
                     i != subset_sums[sz].wicked_end(); ++i) {
                    uint64_t x = *i;
                    if (x == 0 && sz > 1) {
                        // These were fake entries we added earlier
                        continue;
                    }
                    uint64_t d = gcd(x, sz);
                    denom_subgroups[sz / d].push_back(x / d);
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
                            DEBUG_MORE(" %zu", denom_subgroups[i].size());
                            denom_groups[i].emplace_back(move(denom_subgroups[i]));
                        }
                    }
                    DEBUG_MORE("\n");
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
    }
    DEBUG("\n");

    // Merge sequences for each denominator
    size_t S_5_size = 0;
    {
        mutex pool_mutex;
        vector <size_t> merge_jobs;
        for (size_t i = 1; i < denom_groups.size(); ++i) {
            merge_jobs.push_back(i);
        }
        auto larger_group = [&](const list <ChunkedIntSet>::iterator& i1,
                                const list <ChunkedIntSet>::iterator& i2) {
            return i1->size() > i2->size();
        };
        auto worker = [&]() {
            for (;;) {
                size_t denom;
                {   lock_guard <mutex> lock(pool_mutex);
                    if (merge_jobs.empty()) {
                        return;
                    }
                    denom = merge_jobs.back();
                    merge_jobs.pop_back();
                }
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
                        if (i1 == group1->wicked_end()) {
                            if (i2 == group2->wicked_end()) {
                                break;
                            } else {
                                merged_group.push_back(*i2);
                                ++i2;
                            }
                        } else if (i2 == group2->wicked_end()) {
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

                // Size for this denom
                {   lock_guard <mutex> lock(pool_mutex);
                    size_t denom_count = 0, mem = 0;
                    if (!merge_queue.empty()) {
                        denom_count += merge_queue.top()->size();
                        mem += merge_queue.top()->capacity();
                    }
                    DEBUG("Merged denominator %zu: %zu elems, mem %zu K\n",
                          denom, denom_count, mem / 1024);

                    if (false) {
                        // Print everything
                        if (!merge_queue.empty()) {
                            DEBUG("Elems:");
                            for (uint64_t x: *merge_queue.top()) {
                                uint64_t d = gcd(x, denom * S_4_denom);
                                DEBUG_MORE(" %zu/%zu", x / d, denom * S_4_denom / d);
                            }
                            DEBUG_MORE("\n");
                        }
                    }
                    S_5_size += denom_count;
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
        "       %1$s -t [intset|dryrun_s4]\n";

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

    list_S5(S_4);
}
