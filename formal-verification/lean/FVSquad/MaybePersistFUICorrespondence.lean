import FVSquad.MaybePersistFUI

/-!
# MaybePersistFUI Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

Static correspondence validation for `firstUpdateIndex` derivation and
`maybePersistFui` via `#guard` assertions evaluated at `lake build` time.

## Strategy (Task 8, Route B)

The `#guard` cases here are mirrored in
`src/raft_log.rs::test_maybe_persist_fui_correspondence`.

- **Lean side**: `#guard` evaluates at lake-build / compile time.
- **Rust side**: `assert_eq!` in `test_maybe_persist_fui_correspondence`.

## Rust `first_update_index` behaviour

```rust
// src/raft_log.rs lines 560–565
let first_update_index = match &self.unstable.snapshot {
    Some(s) => s.get_metadata().index,  // FUI = snap.index
    None => self.unstable.offset,        // FUI = offset
};
```

## Test groups

### Group A — `firstUpdateIndex` direct (4 cases)

| ID | snapshotIndex | offset | expected FUI |
|----|---------------|--------|--------------|
| A1 | none          | 7      | 7            |
| A2 | some 3        | 7      | 3            |
| A3 | some 0        | 10     | 0            |
| A4 | some 6        | 6      | 6 (=offset)  |

### Group B — `maybePersistFui` no-snapshot path (8 cases)

Fixture: no snapshot, offset=7, logTerm=(4→1, 5→2, 6→3), persisted=3.
FUI = offset = 7 in all B-cases.

| ID | index | term | expected | reason |
|----|-------|------|----------|--------|
| B1 | 5     | 2    | true     | all guards pass |
| B2 | 3     | 2    | false    | guard 1: 3 ≤ 3 |
| B3 | 7     | 3    | false    | guard 2: 7 ≥ FUI(7) |
| B4 | 5     | 99   | false    | guard 3: term mismatch |
| B5 | 4     | 1    | true     | all guards pass |
| B6 | 6     | 3    | true     | all guards pass |
| B7 | 8     | 1    | false    | guard 2: 8 ≥ FUI(7) |
| B8 | 6     | 1    | false    | guard 3: wrong term |

### Group C — `maybePersistFui` snapshot path (8 cases)

Fixture: snapshot at index 3, offset=7, same logTerm, persisted=0.
FUI = snapIdx = 3 in all C-cases.

| ID | index | term | expected | reason |
|----|-------|------|----------|--------|
| C1 | 2     | 2    | true     | all guards pass (2 < FUI=3) |
| C2 | 3     | 2    | false    | guard 2: 3 ≥ FUI(3) — snap blocks |
| C3 | 4     | 1    | false    | guard 2: 4 ≥ FUI(3) — snap blocks |
| C4 | 1     | 99   | false    | guard 3: term mismatch |
| C5 | 0     | 0    | false    | guard 1: 0 ≤ persisted(0) |
| C6 | 2     | 1    | false    | guard 3: wrong term (logTerm 2 = 0 ≠ 1) |
| C7 | 1     | 0    | true     | all guards pass (1 < FUI=3, logTerm 1=0) |
| C8 | 5     | 2    | false    | guard 2: 5 ≥ FUI(3) — snap blocks |

-/

open FVSquad.MaybePersistFUI
open FVSquad.MaybePersist

/-! ## Log-term fixture (shared with MaybePersistCorrespondence) -/

/-- Term function: entries at indices 4, 5, 6 with terms 1, 2, 3.
    All other indices return 0. -/
private def fuitestLogTerm : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | _ => 0

/-! ## Group A — firstUpdateIndex -/

-- A1: No snapshot → FUI = offset
#guard firstUpdateIndex none 7 == 7

-- A2: Snapshot at 3, offset=7 → FUI = 3
#guard firstUpdateIndex (some 3) 7 == 3

-- A3: Snapshot at 0, offset=10 → FUI = 0
#guard firstUpdateIndex (some 0) 10 == 0

-- A4: Snapshot at 6, offset=6 → FUI = 6 (FUI = offset in degenerate case)
#guard firstUpdateIndex (some 6) 6 == 6

/-! ## Group B — maybePersistFui no-snapshot path (FUI = offset = 7) -/

-- B1: All guards pass → true, advances to 5
#guard (maybePersistFui 3 none 7 fuitestLogTerm 5 2).2 == true
#guard (maybePersistFui 3 none 7 fuitestLogTerm 5 2).1 == 5

-- B2: Guard 1 fails — index (3) not > persisted (3)
#guard (maybePersistFui 3 none 7 fuitestLogTerm 3 2).2 == false

-- B3: Guard 2 fails — index (7) = FUI (7), not strictly less
#guard (maybePersistFui 3 none 7 fuitestLogTerm 7 3).2 == false

-- B4: Guard 3 fails — term mismatch (logTerm 5 = 2, arg = 99)
#guard (maybePersistFui 3 none 7 fuitestLogTerm 5 99).2 == false

-- B5: All guards pass at index 4 → true, advances to 4
#guard (maybePersistFui 3 none 7 fuitestLogTerm 4 1).2 == true
#guard (maybePersistFui 3 none 7 fuitestLogTerm 4 1).1 == 4

-- B6: All guards pass at index 6 → true, advances to 6
#guard (maybePersistFui 3 none 7 fuitestLogTerm 6 3).2 == true
#guard (maybePersistFui 3 none 7 fuitestLogTerm 6 3).1 == 6

-- B7: Guard 2 fails — index (8) > FUI (7)
#guard (maybePersistFui 3 none 7 fuitestLogTerm 8 1).2 == false

-- B8: Guard 3 fails — wrong term for index 6 (logTerm 6 = 3, arg = 1)
#guard (maybePersistFui 3 none 7 fuitestLogTerm 6 1).2 == false

/-! ## Group C — maybePersistFui snapshot path (FUI = snapIdx = 3) -/

-- C1: All guards pass — index (2) > persisted (0), 2 < FUI (3), logTerm 2 = 0
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 2 0).2 == true
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 2 0).1 == 2

-- C2: Guard 2 fails — snap blocks: index (3) = FUI (3), not < FUI
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 3 2).2 == false

-- C3: Guard 2 fails — snap blocks: index (4) > FUI (3)
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 4 1).2 == false

-- C4: Guard 3 fails — term mismatch (logTerm 1 = 0, arg = 99)
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 1 99).2 == false

-- C5: Guard 1 fails — index (0) not > persisted (0)
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 0 0).2 == false

-- C6: Guard 3 fails — logTerm 2 = 0, arg = 1 (mismatch)
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 2 1).2 == false

-- C7: All guards pass — index (1) > 0, 1 < FUI (3), logTerm 1 = 0 = term
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 1 0).2 == true
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 1 0).1 == 1

-- C8: Guard 2 fails — snap blocks: index (5) > FUI (3)
#guard (maybePersistFui 0 (some 3) 7 fuitestLogTerm 5 2).2 == false
