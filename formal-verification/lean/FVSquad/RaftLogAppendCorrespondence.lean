import FVSquad.RaftLogAppend

/-!
# RaftLogAppend Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `raftLogAppend` (and
the underlying `truncateAndAppend`) via `#guard` assertions that run the Lean model
on concrete test cases at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases here are mirrored in
`src/raft_log.rs::test_raft_log_append_correspondence` (Rust source side).
Both sides must produce the same expected values on the same inputs.

- **Lean side**: `#guard` evaluates the Lean model at lake-build time.
- **Rust side**: `assert_eq!` in the test verifies at `cargo test` time.

Together they demonstrate that the Lean model and the Rust implementation
agree on 21 correspondence cases covering the three structural branches of
`truncate_and_append` (append, replace, truncate+append), plus cross-checks
for the invariants proved in `RaftLogAppend.lean` (RA4/RA5).

## Definitions (from RaftLogAppend.lean)

```lean
def raftLogAppend (rl : RaftLog) (ents : List Entry) : RaftLog × Nat
def raftLastIndex (rl : RaftLog) : Nat
```

Where `Entry := Nat × Nat` (index, term) and `RaftLog.unstable : Unstable`
has `offset : Nat` and `entries : List Nat` (terms only).

## Fixtures

### Base log (`baseLog`)
Stable storage contains entries at indices 1→term1, 2→term2.
Unstable segment is empty at `offset = 3` (= stable last_index + 1).
This mirrors the Rust fixture built by `test_append` in `src/raft_log.rs`.

```
stable:   index 1→term1, 2→term2    (stableLastIdx = 2)
unstable: offset = 3, entries = []
committed = 0
```

### Extended log (`extLog`)
Same stable storage, plus two unstable entries already in flight:
indices 3→term2, 4→term3.

```
stable:   index 1→term1, 2→term2    (stableLastIdx = 2)
unstable: offset = 3, entries = [2, 3]   (index 3→term2, 4→term3)
committed = 0
```

## Case table

| ID  | Fixture | Input batch       | Expected lastIdx | Expected unstable offset | Expected unstable entries | Branch |
|-----|---------|-------------------|-----------------|--------------------------|--------------------------|--------|
|  1  | base    | []                | 2               | 3 (unchanged)            | [] (unchanged)           | empty  |
|  2  | base    | [(3,2)]           | 3               | 3                        | [2]                      | append |
|  3  | base    | [(1,2)]           | 1               | 1                        | [2]                      | replace|
|  4  | base    | [(2,3),(3,3)]     | 3               | 2                        | [3,3]                    | replace|
|  5  | ext     | []                | 4               | 3 (unchanged)            | [2,3] (unchanged)        | empty  |
|  6  | ext     | [(5,4)]           | 5               | 3                        | [2,3,4]                  | append |
|  7  | ext     | [(4,4)]           | 4               | 3                        | [2,4]                    | trunc  |
| 8–9 | base    | [(3,2)]           | committed=0, stableLastIdx=2 unchanged              | inv.  |
|10–11| ext     | [(4,4)], [(5,4)]  | committed=0, stableLastIdx=2 unchanged              | inv.  |

Total: 21 `#guard` assertions.

-/

open FVSquad.RaftLogAppend

/-! ## Fixtures -/

/-- Base log: stable has indices 1→term1, 2→term2; unstable is empty at offset 3.
    Mirrors the Rust fixture: `previous_ents = [(1,1),(2,2)]` in storage,
    then `RaftLog::new` → unstable.offset = 3, unstable.entries = []. -/
private def baseLog : RaftLog :=
  { committed := 0
    stableLastIdx := 2
    unstable := { offset := 3, entries := [], snapshot := none } }

/-- Extended log: same stable storage, plus two unstable entries in flight:
    index 3 → term 2, index 4 → term 3.
    Built in Rust by calling `append(&[new_entry(3,2), new_entry(4,3)])` on a
    fresh `RaftLog` backed by stable entries [(1,1),(2,2)]. -/
private def extLog : RaftLog :=
  { committed := 0
    stableLastIdx := 2
    unstable := { offset := 3, entries := [2, 3], snapshot := none } }

/-! ## Cases 1–4: base log (empty unstable at offset 3) -/

-- **Case 1**: empty batch — returns existing last_index (from stableLastIdx = 2)
#guard (raftLogAppend baseLog []).2 == 2

-- **Case 2**: append at end — `after (3) = offset (3) + len (0)` → branch 1 (direct append)
--   result: entries = [2], offset = 3, lastIdx = 3 + 1 - 1 = 3
#guard (raftLogAppend baseLog [(3, 2)]).2 == 3
#guard (raftLogAppend baseLog [(3, 2)]).1.unstable.entries == [2]
#guard (raftLogAppend baseLog [(3, 2)]).1.unstable.offset == 3

-- **Case 3**: replace from index 1 — `after (1) ≤ offset (3)` → branch 2 (replace)
--   result: offset = 1, entries = [2], lastIdx = 1 + 1 - 1 = 1
#guard (raftLogAppend baseLog [(1, 2)]).2 == 1
#guard (raftLogAppend baseLog [(1, 2)]).1.unstable.entries == [2]
#guard (raftLogAppend baseLog [(1, 2)]).1.unstable.offset == 1

-- **Case 4**: replace from index 2 with two entries — `after (2) ≤ offset (3)` → branch 2
--   result: offset = 2, entries = [3, 3], lastIdx = 2 + 2 - 1 = 3
#guard (raftLogAppend baseLog [(2, 3), (3, 3)]).2 == 3
#guard (raftLogAppend baseLog [(2, 3), (3, 3)]).1.unstable.entries == [3, 3]
#guard (raftLogAppend baseLog [(2, 3), (3, 3)]).1.unstable.offset == 2

/-! ## Cases 5–7: extended log (unstable has entries [2, 3] at offset 3) -/

-- **Case 5**: empty batch — returns raftLastIndex extLog = 3 + 2 - 1 = 4
#guard (raftLogAppend extLog []).2 == 4

-- **Case 6**: append at end — `after (5) = offset (3) + len (2)` → branch 1 (direct append)
--   result: entries = [2, 3, 4], offset = 3, lastIdx = 3 + 3 - 1 = 5
#guard (raftLogAppend extLog [(5, 4)]).2 == 5
#guard (raftLogAppend extLog [(5, 4)]).1.unstable.entries == [2, 3, 4]
#guard (raftLogAppend extLog [(5, 4)]).1.unstable.offset == 3

-- **Case 7**: truncate then append — `offset (3) < after (4) < offset + len (5)` → branch 3
--   entries.take(4 - 3 = 1) = [2], then ++ [4] = [2, 4]
--   result: entries = [2, 4], offset = 3, lastIdx = 3 + 2 - 1 = 4
#guard (raftLogAppend extLog [(4, 4)]).2 == 4
#guard (raftLogAppend extLog [(4, 4)]).1.unstable.entries == [2, 4]
#guard (raftLogAppend extLog [(4, 4)]).1.unstable.offset == 3

/-! ## Cross-checks: invariants RA4 (committed unchanged) and RA5 (stableLastIdx unchanged) -/

-- committed is never modified by raftLogAppend (mirrors theorem RA4)
#guard (raftLogAppend baseLog [(3, 2)]).1.committed == 0
#guard (raftLogAppend extLog [(4, 4)]).1.committed == 0

-- stableLastIdx is never modified by raftLogAppend (mirrors theorem RA5)
#guard (raftLogAppend baseLog [(3, 2)]).1.stableLastIdx == 2
#guard (raftLogAppend extLog [(5, 4)]).1.stableLastIdx == 2
