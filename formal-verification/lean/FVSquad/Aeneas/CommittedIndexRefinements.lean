/-!
# Aeneas Integration: Refinement Theorems for `MajorityConfig::committed_index`

Bridges between:
- **Aeneas-generated code** — Lean 4 translation of `committed_index` from
  `src/quorum/majority.rs`, enabled by `--features aeneas` (which replaces the
  `MaybeUninit` + unsafe stack-array with a semantically equivalent `Vec`)
- **FVSquad abstract specification** — `FVSquad.CommittedIndex.committedIndex`,
  already proved to satisfy safety and maximality properties (0 sorry)

## Background

Issue #47 removed the `unsafe` block from `committed_index` by gating it behind
`#[cfg(not(feature = "aeneas"))]` and providing an equivalent safe implementation
under `#[cfg(feature = "aeneas")]`:

```rust
// Safe alternative (--features aeneas):
pub fn committed_index(&self, use_group_commit: bool, l: &impl AckedIndexer) -> (u64, bool) {
    if self.voters.is_empty() { return (u64::MAX, true); }
    let mut matched: Vec<Index> = self.voters.iter()
        .map(|v| l.acked_index(*v).unwrap_or_default())
        .collect();
    matched.sort_by(|a, b| b.index.cmp(&a.index));
    // ... (group-commit logic identical to unsafe version)
}
```

This file provides refinement theorems connecting the Aeneas output to the FVSquad
`CommittedIndex` spec (non-group-commit path only; group-commit is deferred per the
original spec).

## Status

🔧 **Skeleton**: Replace the `axiom` declarations in `AeneasGenerated` with the actual
Aeneas `def` output once the tool has been run.  The `sorry` proofs become real proofs
by unfolding the Aeneas-generated definitions.  See `AENEAS_SETUP.md`.

-/

import Mathlib.Tactic
import FVSquad.MajorityQuorum
import FVSquad.CommittedIndex
import FVSquad.Aeneas.UtilRefinements  -- for AResult, AUsize, AU64

namespace FVSquad.Aeneas.CommittedIndexRefinements

open FVSquad.CommittedIndex
open FVSquad.Aeneas.UtilRefinements (AResult AUsize AU64)

/-! ## Aeneas primitive types used by committed_index

In addition to `AUsize` / `AU64` from UtilRefinements, `committed_index` uses:
- `AU64` for the returned committed index
- `ABool` = `Bool` (Aeneas models Rust `bool` as Lean `Bool`)
- `AHashSet` to model `HashSet<u64>` (the voters set)
- `AAckedIndexer` to model the `AckedIndexer` trait

Since Aeneas cannot yet translate `HashSet` (no stdlib model), the voters set is
provided as an abstract parameter. The refinement theorem is stated for any
finite set of voters.
-/

/-- Aeneas model of `AckedIndexer`: a pure function from voter ID to acked index.
    `None` (voter not yet heard from) is mapped to `0` via `unwrap_or_default()`. -/
abbrev AAckedFn := AU64 → AU64

/-! ## Section: Aeneas-generated definitions (axiomatised)

Replace these `axiom` declarations with the actual Aeneas output once run.
-/

/-- Expected Aeneas translation of `committed_index` (non-group-commit path).

    Rust source: `src/quorum/majority.rs`, `#[cfg(feature = "aeneas")]` branch.
    The `use_group_commit = false` case returns `(committed_idx, false)`.
    The `use_group_commit = true` case is axiomatised separately below.

    **Note on empty voters**: Rust returns `(u64::MAX, true)` for empty configs.
    The Aeneas model returns `(AU64.max, true)` which is `(2^64 - 1, true)`.
    The refinement theorem below handles this by requiring `voters ≠ ∅`. -/
axiom Raft.committedIndex
    (voters : List AU64)   -- Aeneas models HashSet iteration as a list
    (acked  : AAckedFn)
    (useGroupCommit : Bool)
    : AResult (AU64 × Bool)

/-! ## Helper: voter list → FVSquad Finset correspondence -/

/-- Convert an `AAckedFn` (u64 → u64) to a `FVSquad.CommittedIndex.AckedFn` (Nat → Nat). -/
def toNatAcked (f : AAckedFn) : AckedFn := fun n => (f ⟨n, by omega⟩).val

/-- Convert a `List AU64` to a `Finset Nat` (the model used by FVSquad). -/
def toNatFinset (voters : List AU64) : Finset Nat :=
  (voters.map (·.val)).toFinset

/-! ## Correspondence lemmas

These state what the Aeneas `committed_index` computes; they are `sorry`-proved
until the Aeneas output is imported.
-/

/-- When `use_group_commit = false`, `Raft.committedIndex` returns the FVSquad
    `committedIndex` value together with `false`. -/
theorem Raft.committedIndex_no_gc
    (voters : List AU64) (acked : AAckedFn)
    (hne : voters ≠ [])
    (hbound : (FVSquad.CommittedIndex.committedIndex
                (toNatFinset voters) (toNatAcked acked)) < 2 ^ 64) :
    Raft.committedIndex voters acked false =
      .ok (⟨FVSquad.CommittedIndex.committedIndex
              (toNatFinset voters) (toNatAcked acked), hbound⟩,
           false) := by
  sorry

/-- When `voters` is empty, `Raft.committedIndex` returns `(u64::MAX, true)`,
    matching Rust's sentinel for "defer to the other half of a joint quorum". -/
theorem Raft.committedIndex_empty
    (acked : AAckedFn) (useGC : Bool) :
    Raft.committedIndex [] acked useGC = .ok (⟨2^64 - 1, by norm_num⟩, true) := by
  sorry

/-! ## Refinement theorems -/

/-- **committedIndex_refines**: the Aeneas implementation of `committed_index`
    (non-group-commit path) returns the same value as the FVSquad abstract model,
    modulo the `AU64` ↔ `Nat` correspondence. -/
theorem committedIndex_refines
    (voters : List AU64) (acked : AAckedFn)
    (hne : voters ≠ [])
    (hbound : FVSquad.CommittedIndex.committedIndex
                (toNatFinset voters) (toNatAcked acked) < 2 ^ 64)
    (result : AU64 × Bool)
    (hok : Raft.committedIndex voters acked false = .ok result) :
    result.1.val = FVSquad.CommittedIndex.committedIndex
                     (toNatFinset voters) (toNatAcked acked) := by
  rw [Raft.committedIndex_no_gc voters acked hne hbound] at hok
  cases hok
  rfl

/-! ## End-to-end safety corollary

Composing the refinement with FVSquad's `committedIndex_safety` gives the key
end-to-end guarantee: **the actual Rust `committed_index` returns a value that at
least a quorum of voters have acknowledged**, i.e., the safety property of Raft's
commit rule follows from the implementation code.
-/

/-- **committed_index_safety_impl**: the Aeneas-translated `committed_index` result
    is acknowledged by a quorum of voters.

    This follows immediately from `FVSquad.CommittedIndex.committedIndex_safety`
    plus the refinement theorem `committedIndex_refines`. -/
theorem committed_index_safety_impl
    (voters : List AU64) (acked : AAckedFn)
    (hne : voters ≠ [])
    (hcard : (toNatFinset voters).card ≠ 0)
    (hbound : FVSquad.CommittedIndex.committedIndex
                (toNatFinset voters) (toNatAcked acked) < 2 ^ 64)
    (result : AU64 × Bool)
    (hok : Raft.committedIndex voters acked false = .ok result) :
    majority (toNatFinset voters).card ≤
      FVSquad.CommittedIndex.countGe
        (toNatFinset voters) (toNatAcked acked) result.1.val := by
  have hval := committedIndex_refines voters acked hne hbound result hok
  rw [hval]
  exact FVSquad.CommittedIndex.committedIndex_safety
          (toNatFinset voters) (toNatAcked acked) hcard

/-! ## Notes on group-commit

The `use_group_commit = true` branch is **not** refined here; it requires modelling
the `group_id` field of `Index` and the two-group intersection logic.  This is tracked
as Step 4+ in Epic #46.  The non-group-commit refinement above covers the primary
safety-critical path.

-/

end FVSquad.Aeneas.CommittedIndexRefinements
