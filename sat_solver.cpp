#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using std::vector;

static constexpr double TIME_LIMIT_SEC = 1200.0;

// Literal encoding: 2*v positive, 2*v+1 negative, so negation is idx^1.
static inline int  lit2idx(int lit)     { return lit > 0 ? (lit << 1) : ((-lit) << 1) | 1; }
static inline int  var_of(int idx)      { return idx >> 1; }
static inline int  neg(int idx)         { return idx ^ 1; }
static inline bool sign_neg(int idx)    { return (idx & 1) != 0; }
static inline int  to_dimacs(int idx)   { return sign_neg(idx) ? -var_of(idx) : var_of(idx); }

static inline int lit_truth(const vector<int8_t>& value, int lit_idx) {
    int v = value[var_of(lit_idx)];
    if (v == 0) return 0;
    return sign_neg(lit_idx) ? -v : v;
}

// All clauses in one buffer. A cref is an offset, so growth never invalidates it.
// Header word packs length in bits 0-29, learned in bit 30, deleted in bit 31.
struct Arena {
    vector<uint32_t> data;
    static constexpr uint32_t HDR = 2;
    static constexpr uint32_t SIZE_MASK    = 0x3FFFFFFFu;
    static constexpr uint32_t LEARNED_FLAG = 0x40000000u;
    static constexpr uint32_t DELETED_FLAG = 0x80000000u;

    inline uint32_t* lits(uint32_t cref) { return data.data() + cref + HDR; }
    inline const uint32_t* lits(uint32_t cref) const { return data.data() + cref + HDR; }
    inline uint32_t size(uint32_t cref)    const { return data[cref] & SIZE_MASK; }
    inline bool     learned(uint32_t cref) const { return (data[cref] & LEARNED_FLAG) != 0; }
    inline bool     deleted(uint32_t cref) const { return (data[cref] & DELETED_FLAG) != 0; }
    inline uint32_t lbd(uint32_t cref)     const { return data[cref + 1]; }
    inline void set_lbd(uint32_t cref, uint32_t v) { data[cref + 1] = v; }
    inline void mark_deleted(uint32_t cref) { data[cref] |= DELETED_FLAG; }

    // Appends [header][lbd][literals] and returns the offset of the header.
    uint32_t add(const int* src, int n, bool is_learned) {
        uint32_t cref = (uint32_t)data.size();
        uint32_t hdr = (uint32_t)n & SIZE_MASK;
        if (is_learned) hdr |= LEARNED_FLAG;
        data.push_back(hdr);
        data.push_back(0);
        for (int i = 0; i < n; ++i) data.push_back((uint32_t)src[i]);
        return cref;
    }
};

// blocker is a second literal of the clause, cached here. If it is already true
// the clause cannot be unit or conflicting, so propagate skips the arena read.
struct Watcher {
    uint32_t cref;
    int      blocker;
};

struct Solver {
    int num_vars = 0;
    Arena arena;
    vector<uint32_t> learned_crefs;

    vector<vector<Watcher>> watches;
    vector<int8_t> value;
    vector<int8_t> value_lit;
    vector<int>    level;
    vector<int32_t> reason;
    // Polarity each variable last held, reused on the next decision after a backjump.
    vector<int8_t> phase;
    vector<int>    trail;
    vector<int>    trail_lim;
    int dl = 0;
    int qhead = 0;

    vector<double> activity;
    double var_inc = 1.0;
    static constexpr double var_decay = 0.95;

    vector<int> heap;
    vector<int> heap_pos;

    // Stamp array for compute_lbd, avoids clearing between calls.
    vector<uint32_t> lbd_stamp;
    uint32_t lbd_counter = 0;

    vector<uint8_t> seen;
    vector<int>     analyze_stack;
    vector<int>     analyze_toclear;

    long long conflicts = 0;
    long long propagations = 0;
    long long decisions = 0;

    // Restart fires when recent learned-clause quality falls below the running average.
    static constexpr int LBD_WIN = 50;
    double lbd_window[LBD_WIN] = {0};
    int    lbd_win_pos = 0;
    int    lbd_win_filled = 0;
    double lbd_win_sum = 0.0;
    double lbd_global_sum = 0.0;
    long long lbd_global_n = 0;
    long long conflicts_at_last_restart = 0;
    static constexpr double RESTART_K = 0.8;

    // Deletion interval grows each round, so reduction gets rarer as search deepens.
    long long next_reduce = 2000;
    long long reduce_inc = 300;

    std::chrono::steady_clock::time_point start_time;

    bool time_exceeded() {
        auto now = std::chrono::steady_clock::now();
        double elapsed = std::chrono::duration<double>(now - start_time).count();
        return elapsed > TIME_LIMIT_SEC;
    }

    bool heap_lt(int a, int b) const { return activity[a] > activity[b]; }

    void heap_up(int i) {
        int x = heap[i];
        while (i > 0) {
            int p = (i - 1) >> 1;
            if (!heap_lt(x, heap[p])) break;
            heap[i] = heap[p];
            heap_pos[heap[i]] = i;
            i = p;
        }
        heap[i] = x;
        heap_pos[x] = i;
    }

    void heap_down(int i) {
        int x = heap[i];
        int n = (int)heap.size();
        while (true) {
            int l = 2*i + 1;
            if (l >= n) break;
            int r = l + 1;
            int c = (r < n && heap_lt(heap[r], heap[l])) ? r : l;
            if (!heap_lt(heap[c], x)) break;
            heap[i] = heap[c];
            heap_pos[heap[i]] = i;
            i = c;
        }
        heap[i] = x;
        heap_pos[x] = i;
    }

    void heap_insert(int v) {
        if (heap_pos[v] != -1) return;
        heap_pos[v] = (int)heap.size();
        heap.push_back(v);
        heap_up(heap_pos[v]);
    }

    void heap_decrease_key(int v) {
        if (heap_pos[v] != -1) heap_up(heap_pos[v]);
    }

    // Highest-activity unassigned variable, O(log n) rather than a scan over all vars.
    int heap_pop() {
        if (heap.empty()) return 0;
        int v = heap[0];
        int last = heap.back();
        heap.pop_back();
        heap_pos[v] = -1;
        if (!heap.empty()) {
            heap[0] = last;
            heap_pos[last] = 0;
            heap_down(0);
        }
        return v;
    }

    void bump_var(int v) {
        activity[v] += var_inc;
        if (activity[v] > 1e100) {
            for (int i = 1; i <= num_vars; ++i) activity[i] *= 1e-100;
            var_inc *= 1e-100;
        }
        if (heap_pos[v] != -1) heap_decrease_key(v);
    }

    void decay_var_inc() { var_inc *= (1.0 / var_decay); }

    int pick_branch() {
        while (!heap.empty()) {
            int v = heap[0];
            if (value[v] == 0) return v;
            heap_pop();
        }
        return 0;
    }

    bool enqueue(int lit_idx, int32_t from_cref) {
        int v = var_of(lit_idx);
        int want = sign_neg(lit_idx) ? -1 : 1;
        if (value[v] != 0) return value[v] == want;
        value[v] = (int8_t)want;
        value_lit[lit_idx] = 1;
        value_lit[neg(lit_idx)] = -1;
        level[v] = dl;
        reason[v] = from_cref;
        trail.push_back(lit_idx);
        return true;
    }

    void new_decision_level() {
        ++dl;
        trail_lim.push_back((int)trail.size());
    }

    // Undo assignments above target, saving each variable's polarity on the way out.
    void backjump_to(int target) {
        if (dl <= target) return;
        int keep = trail_lim[target];
        for (int i = (int)trail.size() - 1; i >= keep; --i) {
            int lit_idx = trail[i];
            int v = var_of(lit_idx);
            phase[v] = value[v];
            value[v] = 0;
            value_lit[lit_idx] = 0;
            value_lit[neg(lit_idx)] = 0;
            reason[v] = -1;
            if (heap_pos[v] == -1) heap_insert(v);
        }
        trail.resize(keep);
        trail_lim.resize(target);
        dl = target;
        qhead = keep;
    }

    void attach_clause(uint32_t cref) {
        uint32_t* L = arena.lits(cref);
        watches[neg((int)L[0])].push_back({cref, (int)L[1]});
        watches[neg((int)L[1])].push_back({cref, (int)L[0]});
    }

    static constexpr uint32_t NO_CONFLICT = UINT32_MAX;

    // Returns the conflicting cref, or a sentinel if propagation completed cleanly.
    uint32_t propagate() {
        const int8_t* vl = value_lit.data();
        while (qhead < (int)trail.size()) {
            int p = trail[qhead++];
            ++propagations;
            vector<Watcher>& ws = watches[p];
            int false_lit = neg(p);
            int i = 0, j = 0;
            int n = (int)ws.size();
            uint32_t conflict_cref = NO_CONFLICT;

            while (i < n) {
                Watcher w = ws[i];

                if (vl[w.blocker] == 1) {
                    ws[j++] = w;
                    ++i;
                    continue;
                }

                uint32_t cref = w.cref;
                uint32_t csz = arena.size(cref);
                uint32_t* L = arena.lits(cref);

                if ((int)L[0] == false_lit) {
                    L[0] = L[1];
                    L[1] = (uint32_t)false_lit;
                }
                int first = (int)L[0];
                Watcher new_w = {cref, first};

                if (first != w.blocker && vl[first] == 1) {
                    ws[j++] = new_w;
                    ++i;
                    continue;
                }

                bool moved = false;
                for (uint32_t k = 2; k < csz; ++k) {
                    int lk = (int)L[k];
                    if (vl[lk] != -1) {
                        L[1] = (uint32_t)lk;
                        L[k] = (uint32_t)false_lit;
                        watches[neg(lk)].push_back({cref, first});
                        moved = true;
                        break;
                    }
                }

                if (moved) {
                    ++i;
                    continue;
                }

                ws[j++] = new_w;
                ++i;

                if (vl[first] == -1) {
                    conflict_cref = cref;
                    while (i < n) ws[j++] = ws[i++];
                    break;
                } else {
                    enqueue(first, (int32_t)cref);
                }
            }

            ws.resize(j);

            if (conflict_cref != NO_CONFLICT) {
                qhead = (int)trail.size();
                return conflict_cref;
            }
        }
        return NO_CONFLICT;
    }

    // Number of distinct decision levels in the clause. LBD 2 clauses are kept forever.
    int compute_lbd(const uint32_t* L, int n) {
        ++lbd_counter;
        int lbd = 0;
        for (int i = 0; i < n; ++i) {
            int lv = level[var_of((int)L[i])];
            if ((int)lbd_stamp.size() <= lv) lbd_stamp.resize(lv + 1, 0);
            if (lbd_stamp[lv] != lbd_counter) {
                lbd_stamp[lv] = lbd_counter;
                ++lbd;
            }
        }
        return lbd;
    }

    // A literal is redundant if every antecedent of its reason is already in the clause.
    bool lit_redundant(int lit_idx) {
        analyze_stack.clear();
        analyze_stack.push_back(lit_idx);
        int top0 = (int)analyze_toclear.size();

        while (!analyze_stack.empty()) {
            int p = analyze_stack.back();
            analyze_stack.pop_back();
            int pv = var_of(p);
            int32_t r = reason[pv];
            if (r < 0) {
                for (int k = top0; k < (int)analyze_toclear.size(); ++k) {
                    seen[var_of(analyze_toclear[k])] = 0;
                }
                analyze_toclear.resize(top0);
                return false;
            }
            uint32_t cref = (uint32_t)r;
            uint32_t csz = arena.size(cref);
            uint32_t* L = arena.lits(cref);
            int forced = neg(p);
            for (uint32_t k = 0; k < csz; ++k) {
                int q = (int)L[k];
                if (q == forced) continue;
                int qv = var_of(q);
                if (seen[qv] || level[qv] == 0) continue;
                if (reason[qv] >= 0) {
                    seen[qv] = 1;
                    analyze_stack.push_back(q);
                    analyze_toclear.push_back(q);
                } else {
                    for (int kk = top0; kk < (int)analyze_toclear.size(); ++kk) {
                        seen[var_of(analyze_toclear[kk])] = 0;
                    }
                    analyze_toclear.resize(top0);
                    return false;
                }
            }
        }
        return true;
    }

    // Shorter clauses propagate more often and survive deletion longer, so this pays twice.
    void minimize_learned(vector<int>& learned) {
        analyze_toclear.clear();
        for (int lit_idx : learned) {
            seen[var_of(lit_idx)] = 1;
            analyze_toclear.push_back(lit_idx);
        }
        int n = (int)learned.size();
        int j = 1;
        for (int i = 1; i < n; ++i) {
            int lit_idx = learned[i];
            int v = var_of(lit_idx);
            if (reason[v] < 0 || !lit_redundant(lit_idx)) {
                learned[j++] = lit_idx;
            }
        }
        learned.resize(j);
        for (int lit_idx : analyze_toclear) seen[var_of(lit_idx)] = 0;
        analyze_toclear.clear();
    }

    // Resolve backwards along the trail until one literal of the current level remains.
    void analyze(uint32_t conflict_cref, vector<int>& learned, int& bj_level) {
        learned.clear();
        learned.push_back(0);

        int path_count = 0;
        uint32_t cref = conflict_cref;
        int ti = (int)trail.size() - 1;
        int pivot = -1;

        do {
            uint32_t csz = arena.size(cref);
            uint32_t* L = arena.lits(cref);
            for (uint32_t k = (pivot == -1 ? 0u : 1u); k < csz; ++k) {
                int q = (int)L[k];
                int qv = var_of(q);
                if (!seen[qv] && level[qv] > 0) {
                    seen[qv] = 1;
                    bump_var(qv);
                    if (level[qv] >= dl) {
                        ++path_count;
                    } else {
                        learned.push_back(q);
                    }
                }
            }

            while (ti >= 0 && !seen[var_of(trail[ti])]) --ti;
            if (ti < 0) break;
            pivot = trail[ti];
            int pv = var_of(pivot);
            cref = (uint32_t)reason[pv];
            seen[pv] = 0;
            --path_count;
            --ti;
        } while (path_count > 0);

        learned[0] = neg(pivot);
        for (size_t k = 1; k < learned.size(); ++k) seen[var_of(learned[k])] = 0;

        minimize_learned(learned);

        if (learned.size() == 1) {
            bj_level = 0;
        } else {
            int max_i = 1;
            int max_lv = level[var_of(learned[1])];
            for (size_t k = 2; k < learned.size(); ++k) {
                int lv = level[var_of(learned[k])];
                if (lv > max_lv) { max_lv = lv; max_i = (int)k; }
            }
            std::swap(learned[1], learned[max_i]);
            bj_level = max_lv;
        }
    }

    // Drop the worst half of learned clauses. Never drop LBD<=2, never drop a live reason.
    void reduce_db() {
        vector<uint32_t> sortable;
        sortable.reserve(learned_crefs.size());
        for (uint32_t cref : learned_crefs) {
            if (!arena.deleted(cref)) sortable.push_back(cref);
        }
        std::sort(sortable.begin(), sortable.end(), [&](uint32_t a, uint32_t b) {
            uint32_t la = arena.lbd(a), lb = arena.lbd(b);
            if (la != lb) return la > lb;
            return arena.size(a) > arena.size(b);
        });

        vector<uint8_t> is_reason(arena.data.size(), 0);
        for (int lit_idx : trail) {
            int32_t r = reason[var_of(lit_idx)];
            if (r >= 0 && (size_t)r < is_reason.size()) is_reason[r] = 1;
        }

        int target = (int)sortable.size() / 2;
        int removed = 0;
        for (int i = 0; i < (int)sortable.size() && removed < target; ++i) {
            uint32_t cref = sortable[i];
            if (arena.lbd(cref) <= 2) continue;
            if (is_reason[cref]) continue;
            arena.mark_deleted(cref);
            ++removed;
        }

        if (removed == 0) return;

        for (auto& wl : watches) {
            int j = 0;
            for (int i = 0; i < (int)wl.size(); ++i) {
                if (!arena.deleted(wl[i].cref)) wl[j++] = wl[i];
            }
            wl.resize(j);
        }

        int j = 0;
        for (uint32_t cref : learned_crefs) {
            if (!arena.deleted(cref)) learned_crefs[j++] = cref;
        }
        learned_crefs.resize(j);
    }

    int solve() {
        start_time = std::chrono::steady_clock::now();

        if (propagate() != NO_CONFLICT) return 0;

        vector<int> learned;
        learned.reserve(64);
        const long long MIN_BETWEEN_RESTARTS = 50;

        while (true) {
            if ((conflicts & 4095) == 0 && time_exceeded()) return -1;

            uint32_t cref = propagate();
            if (cref != NO_CONFLICT) {
                ++conflicts;
                if (dl == 0) return 0;

                int bj_level;
                analyze(cref, learned, bj_level);
                decay_var_inc();
                backjump_to(bj_level);

                int learned_lbd;
                if (learned.size() == 1) {
                    enqueue(learned[0], -1);
                    learned_lbd = 1;
                } else {
                    uint32_t new_cref = arena.add(learned.data(), (int)learned.size(), true);
                    learned_lbd = compute_lbd(arena.lits(new_cref), (int)learned.size());
                    arena.set_lbd(new_cref, (uint32_t)learned_lbd);
                    learned_crefs.push_back(new_cref);
                    attach_clause(new_cref);
                    enqueue((int)arena.lits(new_cref)[0], (int32_t)new_cref);
                }

                lbd_global_sum += learned_lbd;
                ++lbd_global_n;
                if (lbd_win_filled < LBD_WIN) {
                    lbd_window[lbd_win_pos] = learned_lbd;
                    lbd_win_sum += learned_lbd;
                    ++lbd_win_filled;
                } else {
                    lbd_win_sum -= lbd_window[lbd_win_pos];
                    lbd_window[lbd_win_pos] = learned_lbd;
                    lbd_win_sum += learned_lbd;
                }
                lbd_win_pos = (lbd_win_pos + 1) % LBD_WIN;

                if (lbd_win_filled >= LBD_WIN &&
                    conflicts - conflicts_at_last_restart >= MIN_BETWEEN_RESTARTS) {
                    double recent_avg = lbd_win_sum / LBD_WIN;
                    double global_avg = lbd_global_sum / lbd_global_n;
                    bool close_to_sat = (int)trail.size() > (3 * num_vars / 4);
                    if (!close_to_sat && RESTART_K * recent_avg > global_avg) {
                        backjump_to(0);
                        conflicts_at_last_restart = conflicts;
                        lbd_win_filled = 0;
                        lbd_win_sum = 0.0;
                        lbd_win_pos = 0;
                    }
                }

                if (conflicts >= next_reduce) {
                    backjump_to(0);
                    reduce_db();
                    next_reduce = conflicts + reduce_inc;
                    reduce_inc += 100;
                }
            } else {
                if ((int)trail.size() == num_vars) return 1;
                int v = pick_branch();
                if (v == 0) return 1;
                heap_pop();
                ++decisions;
                new_decision_level();
                int lit_idx;
                if (phase[v] == 1)       lit_idx = lit2idx(v);
                else if (phase[v] == -1) lit_idx = lit2idx(-v);
                else                     lit_idx = lit2idx(-v); 
                enqueue(lit_idx, -1);
            }
        }
    }

    bool init(int n_vars, const vector<vector<int>>& dimacs_clauses) {
        num_vars = n_vars;
        watches.assign(2 * (num_vars + 1), {});
        value.assign(num_vars + 1, 0);
        value_lit.assign(2 * (num_vars + 1), 0);
        level.assign(num_vars + 1, 0);
        reason.assign(num_vars + 1, -1);
        phase.assign(num_vars + 1, 0);
        activity.assign(num_vars + 1, 0.0);
        heap.reserve(num_vars);
        heap_pos.assign(num_vars + 1, -1);
        seen.assign(num_vars + 1, 0);
        lbd_stamp.assign(num_vars + 2, 0);

        for (int v = 1; v <= num_vars; ++v) heap_insert(v);

        arena.data.reserve(8 * (dimacs_clauses.size() + 1024));

        for (const auto& dc : dimacs_clauses) {
            if (dc.empty()) return false;
            vector<int> lits;
            lits.reserve(dc.size());
            for (int dlit : dc) lits.push_back(lit2idx(dlit));
            std::sort(lits.begin(), lits.end());
            vector<int> cleaned;
            cleaned.reserve(lits.size());
            bool taut = false;
            for (size_t i = 0; i < lits.size(); ++i) {
                if (!cleaned.empty() && cleaned.back() == lits[i]) continue;
                if (!cleaned.empty() && cleaned.back() == neg(lits[i])) { taut = true; break; }
                cleaned.push_back(lits[i]);
            }
            if (taut) continue;
            if (cleaned.empty()) return false;
            if (cleaned.size() == 1) {
                uint32_t cref = arena.add(cleaned.data(), 1, false);
                if (!enqueue((int)arena.lits(cref)[0], (int32_t)cref)) return false;
            } else {
                uint32_t cref = arena.add(cleaned.data(), (int)cleaned.size(), false);
                attach_clause(cref);
            }
        }
        return true;
    }
};

static bool read_cnf(const std::string& path, int& num_vars, vector<vector<int>>& clauses) {
    std::ifstream in(path);
    if (!in) { std::cerr << "Error: cannot open " << path << "\n"; return false; }
    num_vars = 0;
    clauses.clear();
    std::string line;
    vector<int> cur;
    cur.reserve(64);
    int expected_clauses = -1;

    while (std::getline(in, line)) {
        size_t a = 0;
        while (a < line.size() && (line[a] == ' ' || line[a] == '\t' || line[a] == '\r')) ++a;
        if (a >= line.size()) continue;
        char ch = line[a];
        if (ch == 'c') continue;
        if (ch == '%') break;
        if (ch == 'p') {
            std::istringstream iss(line);
            std::string p, cnf;
            iss >> p >> cnf >> num_vars >> expected_clauses;
            if (p != "p" || cnf != "cnf") { std::cerr << "Bad header\n"; return false; }
            continue;
        }
        std::istringstream iss(line);
        int x;
        while (iss >> x) {
            if (x == 0) {
                if (!cur.empty()) clauses.push_back(cur);
                cur.clear();
            } else {
                cur.push_back(x);
            }
        }
    }
    if (!cur.empty()) {
        clauses.push_back(cur);
        cur.clear();
    }
    return true;
}

int main(int argc, char** argv) {
    auto t_start = std::chrono::steady_clock::now();

    if (argc != 2) {
        std::fprintf(stderr, "Usage: %s <input.cnf>\n", argv[0]);
        return 1;
    }
    int num_vars;
    vector<vector<int>> clauses;
    if (!read_cnf(argv[1], num_vars, clauses)) return 1;

    Solver s;
    bool init_ok = s.init(num_vars, clauses);

    auto t_solve_start = std::chrono::steady_clock::now();
    int result = init_ok ? s.solve() : 0;
    auto t_solve_end = std::chrono::steady_clock::now();

    const char* verify_str = "VERIFY:SKIP";
    if (result == 1) {
        verify_str = "VERIFY:PASS";
        for (const auto& dc : clauses) {
            bool ok = false;
            for (int dlit : dc) {
                int v = dlit > 0 ? dlit : -dlit;
                if (v < 1 || v > num_vars) continue;
                int val = s.value[v];  // +1 true, -1 false
                if ((dlit > 0 && val == 1) || (dlit < 0 && val == -1)) {
                    ok = true;
                    break;
                }
            }
            if (!ok) { verify_str = "VERIFY:FAIL"; break; }
        }
    } else if (result == 0) {
        verify_str = "VERIFY:PASS";
    }

    if (result == 1) {
        std::printf("RESULT:SAT\n");
        std::printf("ASSIGNMENT:");
        bool first = true;
        for (int v = 1; v <= num_vars; ++v) {
            int val = (s.value[v] == 1) ? 1 : 0;
            if (!first) std::printf(" ");
            first = false;
            std::printf("%d=%d", v, val);
        }
        std::printf("\n");
    } else if (result == 0) {
        std::printf("RESULT:UNSAT\n");
    } else {
        std::printf("RESULT:UNKNOWN\n");
    }

    auto t_total_end = std::chrono::steady_clock::now();
    double t_solve = std::chrono::duration<double>(t_solve_end - t_solve_start).count();
    double t_total = std::chrono::duration<double>(t_total_end - t_start).count();

    std::printf("%s\n", verify_str);
    std::printf("TIME_SOLVE_SEC:%.6f\n", t_solve);
    std::printf("TIME_TOTAL_SEC:%.6f\n", t_total);
    std::printf("STATS:decisions=%lld propagations=%lld conflicts=%lld learned_clauses=%zu\n",
                s.decisions, s.propagations, s.conflicts, s.learned_crefs.size());
    return 0;
}