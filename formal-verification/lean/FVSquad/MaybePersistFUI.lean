import FVSquad.MaybePersist

/-!
# MaybePersistFUI — Concrete `firstUpdateIndex` Derivation from Unstable

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

Extends the abstract `MaybePersist` model by formalising the **concrete
derivation** of `firstUpdateIndex` from the `Unstable` struct fields.

## Rust source

```rust
// src/raft_log.rs, lines 560–565
let first_update_index = match &self.unstable.snapshot {
    Some(s) => s.get_metadata().index,
    None => self.unstable.offset,
};
```

`firstUpdateIndex` depends on two fields of `Unstable`:

| Lean field          | Rust field               | Meaning |
|---------------------|--------------------------|---------|
| `snapshotIndex`     | `unstable.snapshot?.metadata.index` | Pending snapshot index, if any |
| `offset`            | `unstable.offset`        | Base index of the in-memory entry slice |

## Model scope

The `Unstable` struct is modelled here only by the two fields that
affect `firstUpdateIndex`.  In particular we abstract away:

- `Unstable.entries` (the in-memory entry slice)
- `Unstable.logger`
- Concurrency and `&self` vs `&mut self` distinctions

## Unstable invariant

A key invariant of `Unstable` is that when a snapshot is present, its
index is **strictly less than** `offset` (the entries' base index):

> `snap.metadata.index < unstable.offset`

This is preserved by `restore`, `stable_entries`, `stable_snap`, and
`truncate_and_append`.  When the invariant holds, `firstUpdateIndex < offset`.

## What This File Provides

| ID  | Name                                      | Status    | Description |
|-----|-------------------------------------------|-----------|-------------|
| FU1 | `fui_snap_case`                           | ✅ proved | FUI = `snap.index` when snapshot present |
| FU2 | `fui_no_snap_case`                        | ✅ proved | FUI = `offset` when no snapshot |
| FU3 | `fui_snap_lt_offset`                      | ✅ proved | Invariant: `snap.idx < offset → FUI < offset` |
| FU4 | `maybePersistFui_eq_abstract`             | ✅ proved | Concrete model equals abstract with derived FUI |
| FU5 | `maybePersistFui_monotone`                | ✅ proved | `persisted` never decreases |
| FU6 | `maybePersistFui_true_iff`                | ✅ proved | Full advance characterisation |
| FU7 | `maybePersistFui_snap_blocks_advance_at`  | ✅ proved | Snapshot at `idx` prevents advancing to `idx` |
| FU8 | `maybePersistFui_no_snap_uses_offset`     | ✅ proved | No-snapshot path uses `offset` as the FUI bound |

**Sorry count**: 0.  All theorems proved without `sorry`.

-/

namespace FVSquad.MaybePersistFUI

open FVSquad.MaybePersist

-- ---------------------------------------------------------------------------
-- Core definition
-- ---------------------------------------------------------------------------

/--
`firstUpdateIndex snapshotIndex offset` computes the concrete value
of `first_update_index` from `src/raft_log.rs`:

```rust
let first_update_index = match &self.unstable.snapshot {
    Some(s) => s.get_metadata().index,
    None => self.unstable.offset,
};
```

Models `Unstable` abstractly as `(snapshotIndex : Option Nat, offset : Nat)`.
-/
def firstUpdateIndex (snapshotIndex : Option Nat) (offset : Nat) : Nat :=
  snapshotIndex.getD offset

/--
`maybePersistFui` is the concrete version of `maybePersist` where
`firstUpdateIndex` is derived from the `Unstable` fields rather than
passed as an explicit parameter.
-/
def maybePersistFui (persisted : Nat) (snapshotIndex : Option Nat) (offset : Nat)
    (logTerm : Nat → Nat) (index term : Nat) : Nat × Bool :=
  maybePersist persisted (firstUpdateIndex snapshotIndex offset) logTerm index term

-- ---------------------------------------------------------------------------
-- FU1: snapshot case
-- ---------------------------------------------------------------------------

/-- **FU1** When a snapshot is present, `firstUpdateIndex` equals the
    snapshot's index.  Corresponds to the `Some(s) => s.get_metadata().index`
    branch in Rust. -/
theorem fui_snap_case (idx offset : Nat) :
    firstUpdateIndex (some idx) offset = idx := by
  simp [firstUpdateIndex]

-- ---------------------------------------------------------------------------
-- FU2: no-snapshot case
-- ---------------------------------------------------------------------------

/-- **FU2** When no snapshot is present, `firstUpdateIndex` equals `offset`.
    Corresponds to the `None => self.unstable.offset` branch in Rust. -/
theorem fui_no_snap_case (offset : Nat) :
    firstUpdateIndex none offset = offset := by
  simp [firstUpdateIndex]

-- ---------------------------------------------------------------------------
-- FU3: Unstable invariant implies FUI < offset
-- ---------------------------------------------------------------------------

/-- **FU3** When the `Unstable` invariant holds (`snap.index < offset`),
    the derived `firstUpdateIndex` is strictly less than `offset`.

    This reflects the invariant maintained by `Unstable::restore`,
    `stable_snap`, and `truncate_and_append`. -/
theorem fui_snap_lt_offset (idx offset : Nat) (h : idx < offset) :
    firstUpdateIndex (some idx) offset < offset := by
  simp [firstUpdateIndex, h]

-- ---------------------------------------------------------------------------
-- FU4: Equivalence with the abstract model
-- ---------------------------------------------------------------------------

/-- **FU4** The concrete model `maybePersistFui` is definitionally equal to
    the abstract `maybePersist` when the latter is given the derived FUI.
    This makes all `MaybePersist` theorems available for the concrete form. -/
theorem maybePersistFui_eq_abstract
    (persisted : Nat) (snapshotIndex : Option Nat) (offset : Nat)
    (logTerm : Nat → Nat) (index term : Nat) :
    maybePersistFui persisted snapshotIndex offset logTerm index term =
    maybePersist persisted (firstUpdateIndex snapshotIndex offset) logTerm index term := by
  rfl

-- ---------------------------------------------------------------------------
-- FU5: Monotonicity
-- ---------------------------------------------------------------------------

/-- **FU5** The concrete `persisted` value never decreases: the result of
    `maybePersistFui` is always ≥ the input `persisted`. -/
theorem maybePersistFui_monotone
    (persisted : Nat) (snapshotIndex : Option Nat) (offset : Nat)
    (logTerm : Nat → Nat) (index term : Nat) :
    persisted ≤ (maybePersistFui persisted snapshotIndex offset logTerm index term).1 := by
  simp [maybePersistFui]
  exact maybePersist_monotone persisted (firstUpdateIndex snapshotIndex offset) logTerm index term

-- ---------------------------------------------------------------------------
-- FU6: Full advance characterisation
-- ---------------------------------------------------------------------------

/-- **FU6** `maybePersistFui` returns `true` (and advances `persisted`) if and
    only if all three guards hold:
    1. `index > persisted`
    2. `index < firstUpdateIndex snapshotIndex offset`
    3. `logTerm index = term`

    Lifts `maybePersist_true_iff` to the concrete FUI derivation. -/
theorem maybePersistFui_true_iff
    (persisted : Nat) (snapshotIndex : Option Nat) (offset : Nat)
    (logTerm : Nat → Nat) (index term : Nat) :
    (maybePersistFui persisted snapshotIndex offset logTerm index term).2 = true ↔
    index > persisted ∧ index < firstUpdateIndex snapshotIndex offset ∧ logTerm index = term := by
  simp [maybePersistFui, maybePersist_true_iff, guardsHold]

-- ---------------------------------------------------------------------------
-- FU7: Snapshot blocks advance at (or above) snap.index
-- ---------------------------------------------------------------------------

/-- **FU7** When a snapshot is pending at `snapIdx`, no call to `maybePersistFui`
    can advance `persisted` to `snapIdx` or beyond.

    Formally: if `index ≥ snapIdx` then `maybePersistFui` returns `false`.

    This is the safety property that prevents committing entries from a
    stale log batch when a newer snapshot has arrived. -/
theorem maybePersistFui_snap_blocks_advance_at
    (persisted snapIdx offset : Nat) (logTerm : Nat → Nat) (index term : Nat)
    (h : index ≥ snapIdx) :
    (maybePersistFui persisted (some snapIdx) offset logTerm index term).2 = false := by
  simp only [maybePersistFui, maybePersist, firstUpdateIndex, Option.getD]
  split
  · next h2 => omega
  · rfl

-- ---------------------------------------------------------------------------
-- FU8: No-snapshot path uses offset as the upper bound
-- ---------------------------------------------------------------------------

/-- **FU8** When there is no pending snapshot, `maybePersistFui` returns `true`
    if and only if `index > persisted`, `index < offset`, and the term matches.

    This shows that without a snapshot, `offset` (the first unstable entry
    position) acts as the exclusive upper bound for `persisted` advancement. -/
theorem maybePersistFui_no_snap_uses_offset
    (persisted offset : Nat) (logTerm : Nat → Nat) (index term : Nat) :
    (maybePersistFui persisted none offset logTerm index term).2 = true ↔
    index > persisted ∧ index < offset ∧ logTerm index = term := by
  simp [maybePersistFui, maybePersist_true_iff, guardsHold, firstUpdateIndex]

end FVSquad.MaybePersistFUI
