# sat_solver

A conflict-driven clause-learning SAT solver in C++17. Single file, 745 lines,
no dependencies. Reads DIMACS CNF, decides satisfiability, and verifies its own
model before printing it.

The heuristic set is Glucose-class: LBD-scored clause deletion, LBD-triggered
restarts, phase saving, and recursive clause minimization, over an arena
allocator with blocker literals.

## Build and run

```
g++ -O3 -DNDEBUG -std=c++17 -o sat_solver sat_solver.cpp
./sat_solver input.cnf
```

Output is one field per line, machine-readable:

```
RESULT:UNSAT
VERIFY:PASS
TIME_SOLVE_SEC:1.637919
TIME_TOTAL_SEC:1.663204
STATS:decisions=... propagations=... conflicts=... learned_clauses=...
```

`RESULT` is `SAT`, `UNSAT`, or `UNKNOWN` (1200 s limit). `TIME_SOLVE_SEC`
excludes parsing.

## Memory layout

Clauses live in one contiguous `vector<uint32_t>`. A clause reference is an
offset into that buffer, not a pointer, so the arena can grow without
invalidating anything already stored.

```
[ header ][ lbd ][ lit0 ][ lit1 ] ... [ litN ]
  ^cref
```

The header packs three things into 32 bits: the literal count in the low 30
bits, a learned flag at bit 30, and a deleted flag at bit 31. Deletion is
therefore a single OR, with no memory moved and no watch list touched until the
next compaction pass.

Literals are encoded as `2*v` positive and `2*v+1` negative, so negation is
`idx ^ 1` and the variable is `idx >> 1`. Watch lists index directly by
literal.

## Heuristics

**Watched literals with blockers.** Each watcher carries a `blocker`, a second
literal from the same clause cached in the watch list itself. If the blocker is
already true the clause cannot be unit or conflicting, so propagation skips it
without touching the arena at all. This removes most clause dereferences from
the inner loop, which is where a solver spends nearly all its time.

**Conflict analysis to the first UIP.** Resolve backwards along the trail until
exactly one literal from the current decision level remains. Its negation
becomes the asserting literal.

**Recursive clause minimization.** After the 1UIP clause is built, each literal
is tested for redundancy: if every antecedent of its reason is already in the
clause, or is itself redundant, it can be dropped. Implemented iteratively with
an explicit stack rather than by recursion. Shorter learned clauses propagate
more often and survive deletion longer, so this pays twice.

**LBD scoring.** Each learned clause is scored by the number of distinct
decision levels among its literals, computed with a stamp array so no clearing
pass is needed. LBD 2 clauses ("glue") link two levels and are treated as
permanently valuable.

**Clause deletion.** Every `next_reduce` conflicts, learned clauses are sorted
worst-first by LBD, then by length, and the worst half is marked deleted. Two
exemptions: LBD ≤ 2 is never deleted, and no clause currently serving as the
reason for an assignment on the trail is deleted, since removing it would break
conflict analysis. Watch lists are compacted afterwards in a single pass. The
interval starts at 2000 conflicts and grows by 300, then by a further 100 each
round, so reduction becomes rarer as the search deepens.

**LBD-triggered restarts.** Rather than a fixed or Luby schedule, restarts fire
when recent learning gets worse than historical learning: a 50-conflict sliding
window of LBD is compared against the global average, and a restart triggers
when `0.8 * recent_average > global_average`, with at least 50 conflicts since
the last one.

One refinement worth naming: restarts are suppressed when the trail holds more
than three quarters of all variables. Close to a complete assignment, throwing
the trail away is likely to discard a nearly-found solution, so the solver
finishes the descent instead.

**Phase saving.** When a variable is unassigned during a backjump, the polarity
it held is recorded. Later decisions on that variable reuse the saved polarity.
This is what makes restarts cheap: the solver abandons the search path but
keeps what it learned about which side of each variable was working.

**VSIDS on a binary heap.** Activity bumped during conflict analysis, increment
scaled by 1/0.95 per conflict, and all scores rescaled by 1e-100 on overflow.
The heap keeps a position index so a variable's priority can be updated in
place, giving O(log n) selection instead of a linear scan over all variables.

## Verification

On a SAT result every original clause is checked for at least one true literal
before `VERIFY:PASS` is printed. This runs on every SAT answer, not as a debug
option.

The asymmetry is deliberate and worth stating: an UNSAT result also prints
`VERIFY:PASS`, but nothing has been proven. Checking UNSAT means emitting a
DRAT resolution proof and running a checker such as `drat-trim`, which this
solver does not do. On an UNSAT line, `PASS` means "nothing to check".

`verify.py` is included for independent checking. It reparses the CNF from
scratch and tests the printed assignment without sharing any code or data
structure with the solver, because a solver checking its own model is checking
with the same structures that produced it.

## Measured performance

Single core, Intel Xeon @ 2.10 GHz, 3 GB, g++ 13.3.0, `-O3 -DNDEBUG`.

| instance | vars | clauses | result | time (s) |
|---|---|---|---|---|
| uuf100-012 | 100 | 430 | UNSAT | 0.0028 |
| uf150-010 | 150 | 645 | SAT | 0.0038 |
| uuf150-011 | 150 | 645 | UNSAT | 0.0189 |
| uf200-09 | 200 | 860 | SAT | 0.0147 |
| uuf200-010 | 200 | 860 | UNSAT | 0.242 |
| uf250-033 | 250 | 1065 | SAT | 0.578 |
| uuf250-010 | 250 | 1065 | UNSAT | 1.638 |
| 4blocks | 758 | 47,820 | SAT | 0.0058 |
| 2bitadd_10 | 590 | 1,422 | UNSAT | 2.628 |
| ewddr2-10-by-5-8 | 22,500 | 123,329 | SAT | 0.0029 |

## Limitations

- No UNSAT proof emission; see the verification note above.
- No preprocessing or inprocessing: no variable elimination, subsumption, or
  vivification between restarts.
- Single-threaded, no portfolio or clause sharing.
- No incremental solving under assumptions.

## Files

```
sat_solver.cpp   this solver
bench_cpp.sh     benchmark harness producing the tables above
verify.py        independent assignment checker
```
