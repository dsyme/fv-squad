/-!
# MaybePersist — Lean 4 Specification and Implementation Model

Formal specification of `RaftLog::maybe_persist` from `raft-rs` (`src/raft_log.rs`).

`maybe_persist(index, term)` is called when log entries have been durably written to
stable storage.  It advances `self.persisted` to `index` iff the proposed index is:
  1. strictly greater than the current `persisted`,
  2. strictly less than `first_update_index` (the in-flight lower bound), and
  3. confirmed by the storage layer with the correct `term`.

## Model scope and approximations

* **Indices and terms**: `u64` → `Nat` (no overflow modelling).
* **`store.term(idx)`**: modelled as a pure function `storedTerm : Nat → Option Nat`;
  `Ok(t)` → `some t`, any error → `none`.
* **`unstable.snapshot`**: only the `metadata.index` field is relevant; modelled as
  `snapIndex : Option Nat`.
* **`unstable.offset`**: kept as `unstableOffset : Nat`.
* **`first_update_index`**: derived as `snapIndex.getD unstableOffset`.
* **Omitted**: committed/applied/entries fields, I/O, logging, `fatal!` panics,
  `maybe_persist_snap`, the broader `RaftLog` lifecycle.

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Tactic

namespace FVSquad.MaybePersist

/-! ## State Model -/

/-- Abstract model of the `RaftLog` fields relevant to `maybe_persist`. -/
structure MaybePersistState where
  /-- Highest log index durably persisted on this node. -/
  persisted      : Nat
  /-- `unstable.offset`: first index in the in-memory (unstable) buffer. -/
  unstableOffset : Nat
  /-- Index from a pending snapshot's metadata, if one exists.
      When present, this acts as the upper exclusive bound on persisting. -/
  snapIndex      : Option Nat
  /-- Pure model of `store.term(idx)`: returns `some t` if the stable store
      contains term `t` at `idx`, or `none` on any error or absence. -/
  storedTerm     : Nat → Option Nat

/-- **WF**: invariants that `RaftLog` maintains in the real implementation.

    * `persisted_lt_offset`  : `persisted < unstableOffset`
    * `snap_le_offset`       : if a pending snapshot exists, its index ≤ `unstableOffset`

    Together these ensure that `firstUpdateIndex ≤ unstableOffset`. -/
def MaybePersistState.WF (s : MaybePersistState) : Prop :=
  s.persisted < s.unstableOffset ∧
  ∀ si, s.snapIndex = some si → si ≤ s.unstableOffset

/-! ## `first_update_index` -/

/-- The lower bound of entries that may still be in-flight.

    Mirrors:
    ```rust
    let first_update_index = match &self.unstable.snapshot {
        Some(s) => s.get_metadata().index,
        None    => self.unstable.offset,
    };
    ```
    -/
def firstUpdateIndex (s : MaybePersistState) : Nat :=
  s.snapIndex.getD s.unstableOffset

/-- When no snapshot is pending, `firstUpdateIndex = unstableOffset`. -/
theorem firstUpdateIndex_no_snap (s : MaybePersistState) (h : s.snapIndex = none) :
    firstUpdateIndex s = s.unstableOffset := by
  simp [firstUpdateIndex, h]

/-- When a snapshot is pending, `firstUpdateIndex = snap index`. -/
theorem firstUpdateIndex_snap (s : MaybePersistState) (si : Nat) (h : s.snapIndex = some si) :
    firstUpdateIndex s = si := by
  simp [firstUpdateIndex, h]

/-- Under WF, `firstUpdateIndex ≤ unstableOffset`. -/
theorem firstUpdateIndex_le_offset (s : MaybePersistState) (hwf : s.WF) :
    firstUpdateIndex s ≤ s.unstableOffset := by
  simp only [firstUpdateIndex]
  cases hsnap : s.snapIndex with
  | none => simp
  | some si => simp; exact hwf.2 si hsnap

/-! ## `maybe_persist` -/

/-- The guard condition of `maybe_persist`:

    `index > persisted  ∧  index < firstUpdateIndex  ∧  storedTerm(index) = some term` -/
def maybePersistCond (s : MaybePersistState) (index term : Nat) : Prop :=
  s.persisted < index ∧ index < firstUpdateIndex s ∧ s.storedTerm index = some term

instance (s : MaybePersistState) (index term : Nat) :
    Decidable (maybePersistCond s index term) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Model of `RaftLog::maybe_persist`.

    Returns `(new_state, changed)` where `changed = true` iff `persisted` advanced. -/
def maybePersist (s : MaybePersistState) (index term : Nat) :
    MaybePersistState × Bool :=
  if maybePersistCond s index term then
    ({ s with persisted := index }, true)
  else
    (s, false)

/-! ## Key properties -/

/-- **PROP-1**: Returns `true` iff the guard condition holds. -/
theorem maybePersist_true_iff (s : MaybePersistState) (index term : Nat) :
    (maybePersist s index term).2 = true ↔ maybePersistCond s index term := by
  simp [maybePersist]

/-- **PROP-2**: Returns `false` iff the guard condition does not hold. -/
theorem maybePersist_false_iff (s : MaybePersistState) (index term : Nat) :
    (maybePersist s index term).2 = false ↔ ¬maybePersistCond s index term := by
  simp [maybePersist]

/-- **PROP-3**: When the condition holds, new `persisted = index`. -/
theorem maybePersist_persisted_eq (s : MaybePersistState) (index term : Nat)
    (hcond : maybePersistCond s index term) :
    (maybePersist s index term).1.persisted = index := by
  simp [maybePersist, hcond]

/-- **PROP-4**: When the condition does not hold, state is unchanged. -/
theorem maybePersist_unchanged (s : MaybePersistState) (index term : Nat)
    (hcond : ¬maybePersistCond s index term) :
    (maybePersist s index term).1 = s := by
  simp [maybePersist, hcond]

/-- **PROP-5**: `persisted` is non-decreasing. -/
theorem maybePersist_persisted_mono (s : MaybePersistState) (index term : Nat) :
    s.persisted ≤ (maybePersist s index term).1.persisted := by
  simp only [maybePersist]
  split_ifs with h
  · simp; exact Nat.le_of_lt h.1
  · simp

/-- **PROP-6**: `persisted` strictly advances iff the call returns `true`. -/
theorem maybePersist_strict_advance_iff (s : MaybePersistState) (index term : Nat) :
    s.persisted < (maybePersist s index term).1.persisted ↔
    (maybePersist s index term).2 = true := by
  simp only [maybePersist, maybePersistCond]
  split_ifs with h
  · simp; exact h.1
  · simp

/-- **PROP-7**: The call returns `true` iff `persisted` changed. -/
theorem maybePersist_changed_iff (s : MaybePersistState) (index term : Nat) :
    (maybePersist s index term).1.persisted ≠ s.persisted ↔
    (maybePersist s index term).2 = true := by
  simp only [maybePersist, maybePersistCond]
  split_ifs with h
  · simp; exact Nat.ne_of_gt h.1
  · simp

/-- **PROP-8**: If `index ≤ persisted`, the call always returns `false`. -/
theorem maybePersist_le_persisted_false (s : MaybePersistState) (index term : Nat)
    (h : index ≤ s.persisted) :
    (maybePersist s index term).2 = false := by
  simp [maybePersist, maybePersistCond, Nat.not_lt.mpr h]

/-- **PROP-9**: If `index ≥ firstUpdateIndex`, the call always returns `false`. -/
theorem maybePersist_ge_fui_false (s : MaybePersistState) (index term : Nat)
    (h : firstUpdateIndex s ≤ index) :
    (maybePersist s index term).2 = false := by
  simp [maybePersist, maybePersistCond, Nat.not_lt.mpr h]

/-- **PROP-10**: If `storedTerm index ≠ some term`, the call returns `false`. -/
theorem maybePersist_wrong_term_false (s : MaybePersistState) (index term : Nat)
    (h : s.storedTerm index ≠ some term) :
    (maybePersist s index term).2 = false := by
  simp [maybePersist, maybePersistCond, h]

/-- **PROP-11**: `unstableOffset` is unchanged by `maybe_persist`. -/
theorem maybePersist_offset_unchanged (s : MaybePersistState) (index term : Nat) :
    (maybePersist s index term).1.unstableOffset = s.unstableOffset := by
  simp [maybePersist]
  split_ifs <;> simp

/-- **PROP-12**: `snapIndex` is unchanged by `maybe_persist`. -/
theorem maybePersist_snapIndex_unchanged (s : MaybePersistState) (index term : Nat) :
    (maybePersist s index term).1.snapIndex = s.snapIndex := by
  simp [maybePersist]
  split_ifs <;> simp

/-- **PROP-13**: `storedTerm` is unchanged by `maybe_persist`. -/
theorem maybePersist_storedTerm_unchanged (s : MaybePersistState) (index term : Nat) (j : Nat) :
    (maybePersist s index term).1.storedTerm j = s.storedTerm j := by
  simp [maybePersist]
  split_ifs <;> simp

/-- **PROP-14 (WF preservation)**: `maybe_persist` preserves the well-formedness invariant.

    Proof sketch:
    * On success: `index < firstUpdateIndex ≤ unstableOffset` (the last ≤ by WF), so
      new `persisted = index < unstableOffset`.  `snapIndex` and `unstableOffset` are
      unchanged, so the snapshot bound still holds.
    * On failure: state unchanged. -/
theorem maybePersist_wf (s : MaybePersistState) (index term : Nat)
    (hwf : s.WF) :
    (maybePersist s index term).1.WF := by
  simp only [maybePersist, MaybePersistState.WF]
  split_ifs with hcond
  · -- Success branch: new persisted = index
    constructor
    · -- persisted < unstableOffset: index < firstUpdateIndex ≤ unstableOffset
      calc index < firstUpdateIndex s := hcond.2.1
        _ ≤ s.unstableOffset          := firstUpdateIndex_le_offset s hwf
    · -- snap_le_offset: snapIndex unchanged
      intro si hsi
      exact hwf.2 si hsi
  · -- Failure branch: state unchanged
    exact hwf

/-- **PROP-15 (idempotent)**: Calling `maybe_persist` again with the same `(index, term)`
    after a successful call always returns `false`.

    After success, `persisted = index`, so `index > persisted` fails. -/
theorem maybePersist_idempotent (s : MaybePersistState) (index term : Nat)
    (hcond : maybePersistCond s index term) :
    (maybePersist (maybePersist s index term).1 index term).2 = false := by
  simp [maybePersist, hcond, maybePersistCond, Nat.lt_irrefl]

/-- **PROP-16**: A successful call is the unique fixed point:
    the returned state differs from the input iff the call returned `true`. -/
theorem maybePersist_fixed_point (s : MaybePersistState) (index term : Nat) :
    (maybePersist s index term).1 = s ↔ ¬maybePersistCond s index term := by
  constructor
  · intro heq hcond
    have : (maybePersist s index term).1.persisted = index := maybePersist_persisted_eq s index term hcond
    rw [heq] at this
    exact Nat.not_lt.mpr (Nat.le_of_eq this.symm) hcond.1
  · intro hncond
    exact maybePersist_unchanged s index term hncond

end FVSquad.MaybePersist
