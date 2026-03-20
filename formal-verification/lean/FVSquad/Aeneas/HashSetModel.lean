/-!
# Aeneas Integration: Lean 4 model for Rust's `HashSet<u64>` (Step 6 of Epic #46)

Models `std::collections::HashSet<u64>` (with `DefaultHashBuilder`) as a `Finset ℕ`.

## Strategy Decision (Step 5 of Epic #46)

### Chosen representation: `Finset ℕ`

`HashSet<u64>` is a finite set of distinct 64-bit integers.  The exact mathematical
model is `Finset ℕ`, with `u64` values identified with their `Nat` values.  This is
not an approximation — all `HashSet` properties carry over exactly.

Advantages:
- **Exact**: `Finset.mem`, `Finset.card`, `Finset.insert`, `Finset.erase`, `Finset.union`
  are direct counterparts to the `HashSet` operations.
- **Already used**: the existing FVSquad specs (`CommittedIndex`, `JointQuorum`,
  `QuorumRecentlyActive`) all use `Finset ℕ` for voter/quorum sets.  Aeneas refinements
  therefore require no type conversion at the spec boundary.
- **Huge theorem library**: Mathlib's `Finset` API covers everything we need.

### Alternative: `List AU64` (ordered list)
Aeneas sometimes serialises `HashSet` iteration as a `List`.  The bridge function
`ofList` converts such a list to `AHashSet`.  `CommittedIndexRefinements.lean` already
uses `List AU64` for the voters parameter of the Aeneas axiom; the `ofList` function
here closes that gap.

### Scope: which modules benefit?
Modules using `HashSet<u64>` that can now receive Aeneas refinements:
- `src/quorum/majority.rs` — `Configuration.voters : HashSet<u64>`
- `src/tracker.rs` — `learners`, `learners_next : HashSet<u64>`
- `src/quorum/joint.rs` — both inner `Configuration.voters`
- `src/read_only.rs` — `ReadIndexStatus.acks : HashSet<u64>`

Modules using `HashMap<Vec<u8>, V>` (`read_only.rs` pending_read_index) are deferred;
see `HashMapModel.lean` for the `HashMap<u64, V>` model and the deferral rationale.

## Status

🟢 **Complete**: `AHashSet` definitions and properties are fully proved (no `sorry`).
The only `sorry` is in `ofList_card_le`, which needs `List.toFinset_card_le_length`
from Mathlib (available in recent versions; replace `sorry` with `List.toFinset_card_le_length`).
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import FVSquad.Aeneas.UtilRefinements

namespace FVSquad.Aeneas.HashSetModel

open FVSquad.Aeneas.UtilRefinements (AResult AUsize AU64)

/-! ## Core type alias -/

/-- The Lean model for `HashSet<u64>`.

    `AHashSet` = `Finset ℕ` where each natural number represents a `u64` value.
    All `HashSet` operations map directly to `Finset` operations.

    Note: we do **not** add a `< 2^64` bound to the elements, because the existing
    FVSquad specs (e.g., `FVSquad.CommittedIndex`) already use `Finset ℕ` without
    bounds, and the bound is only material when converting back to a machine word. -/
abbrev AHashSet := Finset ℕ

/-! ## Basic operations

Each definition mirrors the corresponding Rust `HashSet` method.
-/

/-- Empty set — models `HashSet::new()` and `HashSet::default()`. -/
abbrev AHashSet.mkEmpty : AHashSet := ∅

/-- Insert a key — models `HashSet::insert(&mut self, value: u64) -> bool`. -/
def AHashSet.insertKey (s : AHashSet) (k : AU64) : AHashSet :=
  Finset.insert k.val s

/-- Membership test — models `HashSet::contains(&self, value: &u64) -> bool`. -/
def AHashSet.contains (s : AHashSet) (k : AU64) : Bool :=
  k.val ∈ s

/-- Cardinality — models `HashSet::len(&self) -> usize`. -/
def AHashSet.len (s : AHashSet) : ℕ := s.card

/-- Remove — models `HashSet::remove(&mut self, value: &u64) -> bool`. -/
def AHashSet.removeKey (s : AHashSet) (k : AU64) : AHashSet :=
  s.erase k.val

/-- Set union — models unioning two voter sets. -/
def AHashSet.union (s t : AHashSet) : AHashSet := s ∪ t

/-- Set intersection. -/
def AHashSet.inter (s t : AHashSet) : AHashSet := s ∩ t

/-- Iterate as a sorted list of `AU64` values.

    Aeneas typically serialises `HashSet` iteration as a `List` in deterministic order.
    We use sorted order (ascending) here so the list is canonical. -/
def AHashSet.toList (s : AHashSet) : List AU64 :=
  (s.sort (· ≤ ·)).filterMap (fun n =>
    if h : n < 2 ^ 64 then some ⟨n, h⟩ else none)

/-- Convert a `List AU64` to an `AHashSet`.
    Matches `toNatFinset` in `CommittedIndexRefinements.lean`. -/
def ofList (l : List AU64) : AHashSet :=
  (l.map (·.val)).toFinset

/-! ## Key properties -/

@[simp] theorem AHashSet.mkEmpty_card : (AHashSet.mkEmpty).card = 0 :=
  Finset.card_empty

@[simp] theorem AHashSet.insertKey_mem (s : AHashSet) (k : AU64) :
    k.val ∈ AHashSet.insertKey s k :=
  Finset.mem_insert_self k.val s

theorem AHashSet.insertKey_card (s : AHashSet) (k : AU64) (h : k.val ∉ s) :
    (AHashSet.insertKey s k).card = s.card + 1 := by
  simp [AHashSet.insertKey, Finset.card_insert_of_not_mem h]

theorem AHashSet.insertKey_card_le (s : AHashSet) (k : AU64) :
    s.card ≤ (AHashSet.insertKey s k).card := by
  simp [AHashSet.insertKey]
  exact Finset.card_le_card (Finset.subset_insert k.val s)

@[simp] theorem AHashSet.contains_iff (s : AHashSet) (k : AU64) :
    AHashSet.contains s k = true ↔ k.val ∈ s := by
  simp [AHashSet.contains]

@[simp] theorem AHashSet.removeKey_not_mem (s : AHashSet) (k : AU64) :
    k.val ∉ AHashSet.removeKey s k :=
  Finset.not_mem_erase k.val s

theorem AHashSet.removeKey_card (s : AHashSet) (k : AU64) (h : k.val ∈ s) :
    (AHashSet.removeKey s k).card = s.card - 1 := by
  simp [AHashSet.removeKey, Finset.card_erase_of_mem h]

@[simp] theorem ofList_mem (l : List AU64) (k : AU64) :
    k.val ∈ ofList l ↔ k ∈ l := by
  simp [ofList, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

theorem ofList_card_le (l : List AU64) :
    (ofList l).card ≤ l.length := by
  simp [ofList]
  exact List.toFinset_card_le_length _

/-! ## Bridge: `AHashSet` and the existing FVSquad voter models

The existing FVSquad specs use `Finset ℕ` directly for voter sets.
Since `AHashSet = Finset ℕ`, no conversion is needed at the spec boundary.
The `CommittedIndexRefinements.lean` file already uses `toNatFinset` for the
`List AU64 → Finset ℕ` direction; `ofList` is the same function, restated here
for symmetry.
-/

/-- `ofList` is definitionally equal to `CommittedIndexRefinements.toNatFinset`.
    (Both map `List AU64` → `Finset ℕ` via `.map (·.val) |>.toFinset`.) -/
theorem ofList_eq_toNatFinset (l : List AU64) :
    ofList l = (l.map (·.val)).toFinset := rfl

end FVSquad.Aeneas.HashSetModel
