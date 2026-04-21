# find_conflict Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Overview

This directory contains **Task 8 Route B** correspondence validation for
`RaftLog::find_conflict` (`src/raft_log.rs`) against its Lean 4 formal model
`FVSquad.FindConflict.findConflict` (`formal-verification/lean/FVSquad/FindConflict.lean`).

**Approach**: Both sides are evaluated on the same 17 fixture cases from `cases.json`.
- **Lean side**: `#guard` assertions in `FindConflictCorrespondence.lean` run the model at
  `lake build` time (compile-time evaluation).
- **Rust side**: `test_find_conflict_correspondence` in `src/raft_log.rs` runs the same
  cases at `cargo test` time.

If both pass, the Lean model and the Rust implementation produce identical results on all
17 cases.

## Directory Contents

| File | Purpose |
|------|---------|
| `cases.json` | Shared fixture: 17 `(log, entries, expected)` test cases |
| `README.md` | This file |

The test code lives in:
- `formal-verification/lean/FVSquad/FindConflictCorrespondence.lean` — Lean side
- `src/raft_log.rs::test_find_conflict_correspondence` — Rust side

## Running the Tests

**Lean side** (compile-time `#guard` assertions):
```bash
cd formal-verification/lean
lake build FVSquad.FindConflictCorrespondence
```
A clean build with no errors means all 17 Lean `#guard` assertions passed.

**Rust side** (runtime assertions):
```bash
cargo test test_find_conflict_correspondence
```

## Test Cases

| ID | Description | Property (Lean theorem) | Expected |
|----|-------------|------------------------|----------|
| 1  | Empty entries | FC1 `findConflict_empty` | 0 |
| 2  | All entries match | FC4a `findConflict_zero_of_all_match` | 0 |
| 3  | Matching suffix | FC4a | 0 |
| 4  | Last entry only | FC9 `findConflict_singleton_match` | 0 |
| 5  | New entries beyond log | FC5 `findConflict_nonzero_witness` | 4 |
| 6  | Prefix match + new entries | FC7 `findConflict_first_mismatch` | 4 |
| 7  | One match + new entries | FC7 | 4 |
| 8  | All new entries | FC2 `findConflict_head_mismatch` | 4 |
| 9  | Conflict at first entry | FC2 | 1 |
| 10 | Match then conflict | FC7 | 2 |
| 11 | Two matches then conflict | FC7 | 3 |
| 12 | Empty log, entry → new | FC5 | 1 |
| 13 | Empty log, empty entries | FC1 | 0 |
| 14 | Singleton match | FC9 | 0 |
| 15 | Singleton mismatch | FC10 `findConflict_singleton_mismatch` | 1 |
| 16 | Deep match prefix + conflict | FC7 | 5 |
| 17 | All entries conflict | FC2 | 1 |

## Correspondence Notes

The Lean model uses an abstract log (`LogTerm := Nat → Option Nat`), while the Rust uses
a real `RaftLog` with entries in `MemStorage`. The `makeLog stored` helper in Lean and
`make_raft_log(stored)` in Rust produce equivalent representations:

| Concept | Lean | Rust |
|---------|------|------|
| Log state | `makeLog [(i,t)]` → `fun idx => if idx==i then some t else none` | `raft_log.append(&[new_entry(i, t)])` |
| Match check | `matchTerm log idx term` | `raft_log.match_term(idx, term)` |
| Scan entries | `findConflict log entries` | `raft_log.find_conflict(&entries)` |
| Out-of-range | `matchTerm` returns `false` (none branch) | `match_term` returns `false` (unwrap_or) |

## Verification Status

Run completed: 2026-04-21

- ✅ Lean side: `lake build FVSquad.FindConflictCorrespondence` — 17 `#guard` assertions pass (0 errors)
- ✅ Rust side: `cargo test test_find_conflict_correspondence` — 17 cases pass

All 17 test cases produce identical results in both implementations.
