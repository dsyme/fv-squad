import FVSquad.MaybeAppend

/-!
# MaybeAppend Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `maybe_append`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/maybe_append/cases.json` are mirrored
both here (Lean model side) and in `src/raft_log.rs::test_maybe_append_correspondence`
(Rust source side).  Both sides must produce identical outputs on the same
`(stored, prevIdx, prevTerm, leaderCommit, entries)` inputs.

- **Lean side**: `#guard` evaluates `maybeAppend` at `lake build` time.
- **Rust side**: `assert_eq!` in the test function verifies the same cases at `cargo test` time.

Together they demonstrate that the Lean model and the Rust implementation agree on all
8 correspondence cases.

## Log encoding

Same as `FindConflictCorrespondence`: `makeLog stored` builds a `LogTerm` from a list of
`(index, term)` pairs.  `mkState stored committed persisted` wraps this into a `RaftState`.

## What is checked

For each case we check three observable properties:
1. **Return value**: `(maybeAppend ...).1 = expected_result` (the `Option (Nat × Nat)`)
2. **Committed**: `(maybeAppend ...).2.committed = expected_committed` after the call
3. **Log state**: `(maybeAppend ...).2.log k = expected_term_at_k` for selected indices

The full `RaftState` cannot be compared with `==` (the `log` field has function type
`Nat → Option Nat`), so we check each observable property individually.

## Test cases (8 total)

| ID | Description | Return value | Committed |
|----|-------------|-------------|-----------|
| 1  | Non-match (wrong term) | none | unchanged 0 |
| 2  | Match, empty entries, ca=0 | some(0,3) | 0 |
| 3  | Match, empty entries, ca=2 | some(0,3) | 2 |
| 4  | Match, all existing entries match | some(0,3) | 2 |
| 5  | Match, new entries beyond log | some(4,5) | 5 |
| 6  | Match, partial match then conflict | some(3,3) | 0 |
| 7  | Singleton log, one new entry | some(2,2) | 0 |
| 8  | Conflict at last entry (term mismatch) | some(3,3) | 0 |
-/

open FVSquad.FindConflict FVSquad.MaybeAppend

namespace FVSquad.MaybeAppendCorrespondence

/-! ## Log construction helpers -/

/-- Build a `LogTerm` from a finite list of `(index, term)` pairs.
    Mirrors `makeLog` from `FindConflictCorrespondence`. -/
def makeLog' (stored : List (Nat × Nat)) : LogTerm :=
  fun idx => (stored.find? fun p => p.1 == idx).map Prod.snd

/-- Build a `List LogEntry` from a list of `(index, term)` pairs. -/
def makeEntries' (pairs : List (Nat × Nat)) : List LogEntry :=
  pairs.map fun p => { index := p.1, term := p.2 }

/-- Build an initial `RaftState` with `stored` log entries and given `committed`/`persisted`. -/
def mkState (stored : List (Nat × Nat)) (committed persisted : Nat) : RaftState :=
  { log := makeLog' stored, committed, persisted }

/-! ## Sanity checks for helpers -/

-- makeLog' sanity: index 2 in [(1,1),(2,2),(3,3)] → some 2
#guard makeLog' [(1,1),(2,2),(3,3)] 2 == some 2
-- makeLog' sanity: index 5 not in log → none
#guard makeLog' [(1,1),(2,2),(3,3)] 5 == none
-- matchTerm sanity: log[(1,1),(2,2),(3,3)] at 3 with term 3 → true
#guard matchTerm (makeLog' [(1,1),(2,2),(3,3)]) 3 3 = true
-- matchTerm sanity: log[(1,1),(2,2),(3,3)] at 1 with term 5 → false (1 ≠ 5)
#guard matchTerm (makeLog' [(1,1),(2,2),(3,3)]) 1 5 = false

/-! ## Case 1: Non-match (wrong prevTerm)

    Stored log: {1→1, 2→2, 3→3}
    prevIdx=1, prevTerm=5 (but log has term 1 at index 1 → mismatch)
    Expected return: none; state unchanged. -/

-- return value is none
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 5 0 (makeEntries' [])).1 == none
-- committed unchanged
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 5 0 (makeEntries' [])).2.committed == 0
-- persisted unchanged
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 5 0 (makeEntries' [])).2.persisted == 0

/-! ## Case 2: Match, empty entries, leaderCommit=0

    Stored log: {1→1, 2→2, 3→3}
    prevIdx=3, prevTerm=3 (matches), no new entries, leaderCommit=0
    conflict=0 (no entries), last_new=3+0=3
    newCommitted = max(0, min(0,3)) = 0 -/

#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 0 (makeEntries' [])).1 == some (0, 3)
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 0 (makeEntries' [])).2.committed == 0
-- log unchanged (no entries appended)
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 0 (makeEntries' [])).2.log 3 == some 3

/-! ## Case 3: Match, empty entries, leaderCommit=2 → committed advances

    Same as Case 2 but leaderCommit=2.
    newCommitted = max(0, min(2,3)) = 2 -/

#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 2 (makeEntries' [])).1 == some (0, 3)
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 2 (makeEntries' [])).2.committed == 2
-- log unchanged
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 2 (makeEntries' [])).2.log 2 == some 2

/-! ## Case 4: Match, all provided entries already in log (no conflict)

    Stored log: {1→1, 2→2, 3→3}
    prevIdx=1, prevTerm=1 (matches), entries=[(2,2),(3,3)], leaderCommit=2
    findConflict: matchTerm(2,2)=true, matchTerm(3,3)=true → conflict=0
    last_new = 1+2=3, newCommitted=max(0,min(2,3))=2 -/

#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 1 2
    (makeEntries' [(2,2),(3,3)])).1 == some (0, 3)
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 1 2
    (makeEntries' [(2,2),(3,3)])).2.committed == 2
-- existing log entries unchanged at 2 and 3
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 1 2
    (makeEntries' [(2,2),(3,3)])).2.log 2 == some 2
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 1 2
    (makeEntries' [(2,2),(3,3)])).2.log 3 == some 3

/-! ## Case 5: Match, new entries beyond log → conflict=4, log extended

    Stored log: {1→1, 2→2, 3→3}
    prevIdx=3, prevTerm=3 (matches), entries=[(4,4),(5,5)], leaderCommit=5
    findConflict: matchTerm(4,4)=(none==some 4)=false → conflict=4
    start = 4-(3+1)=0, append all entries
    last_new=3+2=5, newCommitted=max(0,min(5,5))=5 -/

#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 5
    (makeEntries' [(4,4),(5,5)])).1 == some (4, 5)
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 5
    (makeEntries' [(4,4),(5,5)])).2.committed == 5
-- new entries added to log
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 5
    (makeEntries' [(4,4),(5,5)])).2.log 4 == some 4
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 5
    (makeEntries' [(4,4),(5,5)])).2.log 5 == some 5
-- original entries still present
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 3 3 5
    (makeEntries' [(4,4),(5,5)])).2.log 3 == some 3

/-! ## Case 6: Match, partial match then conflict → log entry overwritten

    Stored log: {1→1, 2→2, 3→3}
    prevIdx=1, prevTerm=1 (matches), entries=[(2,2),(3,5)], leaderCommit=0
    findConflict: matchTerm(2,2)=true; matchTerm(3,5)=(some 3==some 5)=false → conflict=3
    start=3-(1+1)=1, append ents.drop 1=[(3,5)]
    last_new=1+2=3, newCommitted=max(0,min(0,3))=0 -/

#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 1 0
    (makeEntries' [(2,2),(3,5)])).1 == some (3, 3)
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 1 0
    (makeEntries' [(2,2),(3,5)])).2.committed == 0
-- index 3 overwritten with term 5
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 1 0
    (makeEntries' [(2,2),(3,5)])).2.log 3 == some 5
-- index 2 unchanged (it matched)
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 1 1 0
    (makeEntries' [(2,2),(3,5)])).2.log 2 == some 2

/-! ## Case 7: Singleton log, one new entry

    Stored log: {1→1}
    prevIdx=1, prevTerm=1 (matches), entries=[(2,2)], leaderCommit=0
    findConflict: matchTerm(2,2)=(none==some 2)=false → conflict=2
    start=2-(1+1)=0, append [(2,2)]
    last_new=1+1=2 -/

#guard (maybeAppend (mkState [(1,1)] 0 0) 1 1 0 (makeEntries' [(2,2)])).1 == some (2, 2)
#guard (maybeAppend (mkState [(1,1)] 0 0) 1 1 0 (makeEntries' [(2,2)])).2.log 2 == some 2
-- original entry preserved
#guard (maybeAppend (mkState [(1,1)] 0 0) 1 1 0 (makeEntries' [(2,2)])).2.log 1 == some 1

/-! ## Case 8: Conflict at last stored entry (term mismatch)

    Stored log: {1→1, 2→2, 3→3}
    prevIdx=2, prevTerm=2 (matches), entries=[(3,5)], leaderCommit=0
    findConflict: matchTerm(3,5)=(some 3==some 5)=false → conflict=3
    start=3-(2+1)=0, append [(3,5)]
    last_new=2+1=3 -/

#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 2 2 0
    (makeEntries' [(3,5)])).1 == some (3, 3)
-- index 3 overwritten with term 5
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 2 2 0
    (makeEntries' [(3,5)])).2.log 3 == some 5
-- index 2 unchanged
#guard (maybeAppend (mkState [(1,1),(2,2),(3,3)] 0 0) 2 2 0
    (makeEntries' [(3,5)])).2.log 2 == some 2

/-! ## Summary

The 8 correspondence cases above (with ~24 individual `#guard` assertions) verify:

- **Non-match behaviour**: `maybe_append` returns `none` exactly when `match_term` fails
- **Conflict detection**: the Lean `findConflict` model agrees with the Rust on conflict indices
- **Committed advancement**: `committed` is advanced to `min(leaderCommit, last_new)`
- **Log extension**: new entries beyond the stored log are correctly appended
- **Log overwrite**: entries with conflicting terms are replaced by the new values
- **Selective drop**: `ents.drop(conflict - (idx+1))` correctly selects the suffix to append

These cases are independently verified by `test_maybe_append_correspondence` in
`src/raft_log.rs` at runtime. -/

end FVSquad.MaybeAppendCorrespondence
