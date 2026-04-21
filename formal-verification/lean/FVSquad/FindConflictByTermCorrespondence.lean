import FVSquad.FindConflictByTerm

/-!
# FindConflictByTerm Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `find_conflict_by_term`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/find_conflict_by_term/cases.json` are
mirrored both here (Lean model side) and in
`src/raft_log.rs::test_find_conflict_by_term_correspondence`
(Rust source side).  Both sides must produce the same `(expected_index, expected_term)`
pair on the same `(log, index, term)` input.

- **Lean side**: `#guard` evaluates `findConflictByTermFull testLog lastIndex index term == expected`
  at lake-build time.  A compile error means the Lean model gives a different answer.
- **Rust side**: `assert_eq!` in the test function verifies the same expected values at
  `cargo test` time.

Together they demonstrate that the Lean model and the Rust implementation agree on all
12 correspondence cases.

## Log fixture

All in-range cases use the following log (indices 0–5, terms [0, 1, 1, 2, 3, 3]):

```
index: 0  1  2  3  4  5
term:  0  1  1  2  3  3
```

- Index 0 is the **dummy entry** (term = 0): present in Lean via `LogDummyZero`.
  In Rust, `RaftLog::term(0)` returns 0 via `snapshot_metadata` (index=0, term=0).
- Indices 1–5 are stored entries with terms [1, 1, 2, 3, 3].

## Test cases (12 total)

| ID | index | lastIndex | term | expected_index | expected_term | Property |
|----|-------|-----------|------|----------------|---------------|---------|
| 1  | 5     | 5         | 3    | 5              | some 3        | immediate match at last entry |
| 2  | 5     | 5         | 2    | 3              | some 2        | scan back 2 steps (skip 5,4) |
| 3  | 5     | 5         | 1    | 2              | some 1        | scan back 3 steps (skip 5,4,3) |
| 4  | 5     | 5         | 0    | 0              | some 0        | scan to dummy entry |
| 5  | 3     | 5         | 3    | 3              | some 2        | immediate match: term(3)=2 ≤ 3 |
| 6  | 4     | 5         | 2    | 3              | some 2        | scan back 1: term(4)=3 > 2 |
| 7  | 2     | 5         | 2    | 2              | some 1        | immediate match: term(2)=1 ≤ 2 |
| 8  | 1     | 5         | 0    | 0              | some 0        | scan to dummy from index 1 |
| 9  | 0     | 5         | 5    | 0              | some 0        | base case: index 0 returns dummy |
| 10 | 3     | 5         | 1    | 2              | some 1        | term(3)=2 > 1, scan back |
| 11 | 1     | 5         | 2    | 1              | some 1        | immediate match: term(1)=1 ≤ 2 |
| 12 | 10    | 5         | 3    | 10             | none          | out-of-range early return |

All 12 cases are verified by `#guard` below (compile-time, no `sorry`).
-/

open FVSquad.FindConflictByTerm

namespace FVSquad.FindConflictByTermCorrespondence

/-! ## Log fixture -/

/-- Test log: terms [0, 1, 1, 2, 3, 3] at indices [0, 1, 2, 3, 4, 5].
    Mirrors a `RaftLog` with entries `[(1,1),(2,1),(3,2),(4,3),(5,3)]`.
    Index 0 is the dummy entry (term = 0). -/
private def testLog5 : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 3 | _ => 3

/-! ## Sanity checks for log fixture -/

-- Verify dummy entry
#guard testLog5 0 == 0
-- Verify stored entries match Rust log
#guard testLog5 1 == 1
#guard testLog5 3 == 2
#guard testLog5 5 == 3

/-! ## Cases 1–4: scan from last index (5) with various terms -/

-- Case 1: immediate match — term(5) = 3 ≤ 3
#guard findConflictByTermFull testLog5 5 5 3 == (5, some 3)

-- Case 2: scan back 2 steps — term(5)=3>2, term(4)=3>2, term(3)=2≤2
#guard findConflictByTermFull testLog5 5 5 2 == (3, some 2)

-- Case 3: scan back 3 steps — skip 5,4,3; term(2)=1≤1
#guard findConflictByTermFull testLog5 5 5 1 == (2, some 1)

-- Case 4: scan all the way to dummy — every entry has term > 0
#guard findConflictByTermFull testLog5 5 5 0 == (0, some 0)

/-! ## Cases 5–8: scan from intermediate indices -/

-- Case 5: index 3, term 3 — immediate match: term(3)=2 ≤ 3
#guard findConflictByTermFull testLog5 5 3 3 == (3, some 2)

-- Case 6: index 4, term 2 — term(4)=3>2, scan back; term(3)=2≤2
#guard findConflictByTermFull testLog5 5 4 2 == (3, some 2)

-- Case 7: index 2, term 2 — immediate match: term(2)=1 ≤ 2
#guard findConflictByTermFull testLog5 5 2 2 == (2, some 1)

-- Case 8: index 1, term 0 — term(1)=1>0, scan to dummy
#guard findConflictByTermFull testLog5 5 1 0 == (0, some 0)

/-! ## Case 9: base case at index 0 -/

-- Case 9: base case — index 0 always returns (0, some 0)
#guard findConflictByTermFull testLog5 5 0 5 == (0, some 0)

/-! ## Cases 10–11: additional scan scenarios -/

-- Case 10: index 3, term 1 — term(3)=2>1, scan to index 2 where term=1≤1
#guard findConflictByTermFull testLog5 5 3 1 == (2, some 1)

-- Case 11: index 1, term 2 — immediate match: term(1)=1 ≤ 2
#guard findConflictByTermFull testLog5 5 1 2 == (1, some 1)

/-! ## Case 12: out-of-range early return (FCB5) -/

-- Case 12: index 10 > lastIndex 5 → early return (10, none)
#guard findConflictByTermFull testLog5 5 10 3 == (10, none)

end FVSquad.FindConflictByTermCorrespondence
