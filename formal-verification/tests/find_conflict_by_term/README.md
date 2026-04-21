# find_conflict_by_term — Correspondence Test Fixtures

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Purpose

This directory contains the shared fixture cases for **Task 8 Route B** correspondence
validation of `RaftLog::find_conflict_by_term` against the Lean 4 model
`FVSquad.FindConflictByTerm.findConflictByTermFull`.

## Log fixture

All in-range cases (1–11) use a fixed log with entries at indices 1–5 and terms
[1, 1, 2, 3, 3].  Index 0 is the implicit dummy entry (term = 0).

```
index: 0  1  2  3  4  5
term:  0  1  1  2  3  3
```

In Rust: built by `raft_log.append(&[(1,1),(2,1),(3,2),(4,3),(5,3)])`.
In Lean: modelled as `testLog5 : Nat → Nat` in `FindConflictByTermCorrespondence.lean`.

## Cases

See `cases.json` for the full fixture (12 cases).

| ID | index | last_index | term | expected_index | expected_term | Property |
|----|-------|------------|------|----------------|---------------|---------|
| 1  | 5     | 5          | 3    | 5              | 3             | immediate match |
| 2  | 5     | 5          | 2    | 3              | 2             | scan back 2 |
| 3  | 5     | 5          | 1    | 2              | 1             | scan back 3 |
| 4  | 5     | 5          | 0    | 0              | 0             | scan to dummy |
| 5  | 3     | 5          | 3    | 3              | 2             | immediate match (term=2 ≤ 3) |
| 6  | 4     | 5          | 2    | 3              | 2             | one scan back |
| 7  | 2     | 5          | 2    | 2              | 1             | immediate match |
| 8  | 1     | 5          | 0    | 0              | 0             | scan to dummy from 1 |
| 9  | 0     | 5          | 5    | 0              | 0             | base case (index 0) |
| 10 | 3     | 5          | 1    | 2              | 1             | one scan back |
| 11 | 1     | 5          | 2    | 1              | 1             | immediate match |
| 12 | 10    | 5          | 3    | 10             | null          | out-of-range early return |

## How to run

**Lean side** (compile-time `#guard` assertions):
```bash
cd formal-verification/lean
lake build FVSquad.FindConflictByTermCorrespondence
# All 12 #guard assertions verified at build time
```

**Rust side** (runtime `assert_eq!` test):
```bash
cargo test test_find_conflict_by_term_correspondence
# All 12 cases pass
```

## Correspondence level

**Abstraction**: the Lean model `findConflictByTermFull` captures the backward-scan
semantics faithfully on the verified paths.  The following are abstracted away:
- Storage errors (`Err(_)` path in the Rust loop): the Lean model never errors
  because the dummy entry at index 0 always terminates the scan
- `u64` overflow: modelled as `Nat` (no overflow)
- Logging side effects (`warn!` on out-of-range input)
- Group-commit interactions (unused in this function)

Reference: `src/raft_log.rs#L218–L257` and
`formal-verification/lean/FVSquad/FindConflictByTerm.lean`.
