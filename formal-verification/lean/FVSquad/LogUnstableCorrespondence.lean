import FVSquad.LogUnstable

/-!
# LogUnstable Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `log_unstable` operations:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/log_unstable/cases.json` are
mirrored both here (Lean model side) and in
`src/log_unstable.rs::test_log_unstable_correspondence`
(Rust source side).  Both sides must produce the same result on the same
`(offset, entries_terms, snapshot, query)` input.

- **Lean side**: `#guard` evaluates model functions at lake-build time.
- **Rust side**: corresponding `Unstable` methods verified at `cargo test` time.

## Abstraction

The Lean `Unstable` model stores only `(offset, List Nat, Option (Nat × Nat))`:
- `entries[i]` has log index `offset + i` and term `entries[i]`
- `snapshot = some (snap_index, snap_term)` or `none`

The Rust `Unstable` stores full `Entry` objects (index + term + data).
Correspondence holds when: `entries[i].term == lean_terms[i]` and
`entries[i].index == offset + i`.

## Test cases (12 total)

| ID | offset | entries_terms | snapshot | query | expected |
|----|--------|--------------|---------|-------|---------|
| 1  | 5 | [10,20,30] | none | maybeFirstIndex | none |
| 2  | 5 | [] | (4,9) | maybeFirstIndex | some 5 |
| 3  | 5 | [10,20,30] | none | maybeLastIndex | some 7 |
| 4  | 5 | [] | none | maybeLastIndex | none |
| 5  | 5 | [] | (4,9) | maybeLastIndex | some 4 |
| 6  | 5 | [10,20,30] | none | maybeTerm 5 | some 10 |
| 7  | 5 | [10,20,30] | none | maybeTerm 6 | some 20 |
| 8  | 5 | [10,20,30] | none | maybeTerm 7 | some 30 |
| 9  | 5 | [10,20,30] | none | maybeTerm 8 | none (out of range) |
| 10 | 5 | [10,20,30] | none | maybeTerm 4 | none (before offset, no snap) |
| 11 | 5 | [] | (4,9) | maybeTerm 4 | some 9 (snap term) |
| 12 | 5 | [] | (4,9) | maybeTerm 3 | none (before snap) |
-/

namespace FVSquad.LogUnstableCorrespondence

/-- Example: entries at offset 5 with terms [10,20,30], no snapshot -/
private def uEntries : Unstable :=
  { offset := 5, entries := [10, 20, 30], snapshot := none }

/-- Example: empty entries, snapshot at index 4 term 9 -/
private def uSnap : Unstable :=
  { offset := 5, entries := [], snapshot := some (4, 9) }

/-- Example: empty, no snapshot -/
private def uEmpty : Unstable :=
  { offset := 5, entries := [], snapshot := none }

/-! ## Case 1: maybeFirstIndex with entries only (no snapshot) → none -/

#guard maybeFirstIndex uEntries == none

/-! ## Case 2: maybeFirstIndex with snapshot at index 4 → some 5 (= 4 + 1) -/

#guard maybeFirstIndex uSnap == some 5

/-! ## Case 3: maybeLastIndex with entries [10,20,30] at offset 5 → some 7 (= 5 + 3 - 1) -/

#guard maybeLastIndex uEntries == some 7

/-! ## Case 4: maybeLastIndex with empty entries, no snapshot → none -/

#guard maybeLastIndex uEmpty == none

/-! ## Case 5: maybeLastIndex with snapshot, no entries → some 4 (snap index) -/

#guard maybeLastIndex uSnap == some 4

/-! ## Case 6: maybeTerm at offset (index 5) → some 10 (first entry) -/

#guard maybeTerm uEntries 5 == some 10

/-! ## Case 7: maybeTerm at index 6 → some 20 (second entry) -/

#guard maybeTerm uEntries 6 == some 20

/-! ## Case 8: maybeTerm at index 7 → some 30 (third entry) -/

#guard maybeTerm uEntries 7 == some 30

/-! ## Case 9: maybeTerm at index 8 → none (beyond last entry) -/

#guard maybeTerm uEntries 8 == none

/-! ## Case 10: maybeTerm before offset, no snapshot → none -/

#guard maybeTerm uEntries 4 == none

/-! ## Case 11: maybeTerm at snap index 4 when snapshot = some(4,9) → some 9 -/

#guard maybeTerm uSnap 4 == some 9

/-! ## Case 12: maybeTerm before snap index → none -/

#guard maybeTerm uSnap 3 == none

end FVSquad.LogUnstableCorrespondence
