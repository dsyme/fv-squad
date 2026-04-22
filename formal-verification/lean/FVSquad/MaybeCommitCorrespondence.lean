import FVSquad.MaybeCommit

/-!
# MaybeCommit Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `maybe_commit` and
`commit_to` via `#guard` assertions that run the Lean model on concrete test
cases at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases here are mirrored in
`src/raft_log.rs::test_maybe_commit_correspondence` (Rust source side).
Both sides must produce the same `expected` value on the same inputs.

- **Lean side**: `#guard` evaluates the Lean model at lake-build time.
- **Rust side**: `assert_eq!` in the test verifies at `cargo test` time.

Together they demonstrate that the Lean model and the Rust implementation
agree on all 14 correspondence cases.

## Definitions (from MaybeCommit.lean)

```lean
def maybeCommit (log : LogTerm) (committed maxIndex term : Nat) : Nat :=
  if maxIndex > committed ∧ log maxIndex = some term then maxIndex else committed

def commitTo (committed toCommit : Nat) : Nat :=
  max committed toCommit
```

Where `LogTerm = Nat → Option Nat` (from `FVSquad.FindConflict`).

## Log fixture

We use a log with entries at indices 1–5 with terms 1, 1, 2, 2, 3 respectively.
This mirrors the Rust test log constructed by `make_commit_log`:

```
  index:   0   1   2   3   4   5   6+
  term:    -   1   1   2   2   3   none
  committed = 0 (default)
```

## Case table

| ID  | committed | maxIndex | term | Call                     | Expected | Guard |
|-----|-----------|----------|------|--------------------------|----------|-------|
|  1  | 0         | 3        | 2    | maybeCommit 0 3 2        | 3        | pass: advance |
|  2  | 3         | 3        | 2    | maybeCommit 3 3 2        | 3        | no advance: maxIndex = committed |
|  3  | 4         | 3        | 2    | maybeCommit 4 3 2        | 4        | no advance: maxIndex < committed |
|  4  | 0         | 3        | 1    | maybeCommit 0 3 1        | 0        | no advance: term mismatch |
|  5  | 0         | 6        | 1    | maybeCommit 0 6 1        | 0        | no advance: no log entry |
|  6  | 2         | 3        | 2    | maybeCommit 2 3 2        | 3        | advance single step |
|  7  | 1         | 5        | 3    | maybeCommit 1 5 3        | 5        | advance to last entry |
|  8  | 0         | 1        | 1    | maybeCommit 0 1 1        | 1        | advance to first entry |
|  9  | 0         | 1        | 2    | maybeCommit 0 1 2        | 0        | no advance: wrong term at 1 |
| 10  | 0         | 4        | 2    | maybeCommit 0 4 2        | 4        | advance to index 4 |
| 11  | 3         | –        | –    | commitTo 3 5             | 5        | advance |
| 12  | 5         | –        | –    | commitTo 5 3             | 5        | no-op: monotone |
| 13  | 5         | –        | –    | commitTo 5 5             | 5        | no-op: equal |
| 14  | 0         | –        | –    | commitTo 0 3             | 3        | advance from zero |

-/

open FVSquad.MaybeCommit
open FVSquad.FindConflict

/-! ## Log-term fixture -/

/-- `testLog` mirrors the Rust test log: entries at indices 1–5 with
    terms 1, 1, 2, 2, 3 respectively.  All other indices have no entry. -/
private def testLog : LogTerm
  | 1 => some 1
  | 2 => some 1
  | 3 => some 2
  | 4 => some 2
  | 5 => some 3
  | _ => none

/-! ## `maybeCommit` cases (IDs 1–10) -/

-- **Case 1**: maxIndex (3) > committed (0) and log[3] = some 2 = term → advances to 3
#guard maybeCommit testLog 0 3 2 == 3

-- **Case 2**: maxIndex (3) = committed (3) — not strictly greater → no advance
#guard maybeCommit testLog 3 3 2 == 3

-- **Case 3**: maxIndex (3) < committed (4) → no advance
#guard maybeCommit testLog 4 3 2 == 4

-- **Case 4**: Term mismatch — log[3] = some 2, but term arg = 1 → no advance
#guard maybeCommit testLog 0 3 1 == 0

-- **Case 5**: No log entry at maxIndex 6 (log[6] = none) → no advance
#guard maybeCommit testLog 0 6 1 == 0

-- **Case 6**: Single-step advance — committed=2, maxIndex=3, log[3]=some 2, term=2 → 3
#guard maybeCommit testLog 2 3 2 == 3

-- **Case 7**: Advance to last entry — committed=1, maxIndex=5, log[5]=some 3, term=3 → 5
#guard maybeCommit testLog 1 5 3 == 5

-- **Case 8**: Advance to first entry — committed=0, maxIndex=1, log[1]=some 1, term=1 → 1
#guard maybeCommit testLog 0 1 1 == 1

-- **Case 9**: Wrong term at index 1 — log[1]=some 1 but term arg=2 → no advance
#guard maybeCommit testLog 0 1 2 == 0

-- **Case 10**: Advance to index 4 — log[4]=some 2, term=2, committed=0 → 4
#guard maybeCommit testLog 0 4 2 == 4

-- **Idempotent cross-check**: applying maybeCommit twice with same args gives same result
#guard maybeCommit testLog (maybeCommit testLog 0 3 2) 3 2 == 3

-- **Monotone cross-check**: result is always ≥ committed
#guard maybeCommit testLog 0 3 2 ≥ 0
#guard maybeCommit testLog 3 1 1 ≥ 3  -- no advance: maxIndex=1 < committed=3

/-! ## `commitTo` cases (IDs 11–14) -/

-- **Case 11**: Basic advance — commitTo 3 5 = 5
#guard commitTo 3 5 == 5

-- **Case 12**: No-op (monotone) — commitTo 5 3 = 5 (5 ≥ 3)
#guard commitTo 5 3 == 5

-- **Case 13**: No-op (equal) — commitTo 5 5 = 5
#guard commitTo 5 5 == 5

-- **Case 14**: Advance from zero — commitTo 0 3 = 3
#guard commitTo 0 3 == 3
