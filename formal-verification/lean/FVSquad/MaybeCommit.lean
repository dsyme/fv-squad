/-!
# MaybeCommit — Lean 4 Specification and Implementation Model

Formal specification of `RaftLog::maybe_commit` from `raft-rs` (`src/raft_log.rs`).

`maybe_commit(max_index, term)` advances `self.committed` to `max_index` iff:
  1. `max_index > self.committed`  (strict advance), and
  2. `self.term(max_index) = Ok(term)` (log entry exists with the right term).

The term check is Raft's safety gate: a leader may only commit an entry from
its current term; entries from previous terms are committed transitively but
must not be independently proposed.

## Model scope and approximations

* **Indices and terms**: `u64` → `Nat` (no overflow modelling).
* **`self.term(idx)`**: modelled as a pure function `termFn : Nat → Option Nat`;
  `Ok(t)` → `some t`, any error or absence → `none`.
* **`last_index`**: kept as a `Nat` field in the state; used only to state the
  WF invariant.  The model does not track log entries or their terms explicitly —
  `termFn` is an opaque map.
* **`commit_to` inlining**: `commit_to(x)` is just `committed := x` when
  `x > committed` (the only-increase branch is subsumed by the guard).
* **Omitted**: applied, persisted, unstable entries, logger, I/O, `fatal!`
  panics, `commit_to`'s panic on out-of-range, snapshot mechanics.

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Tactic

namespace FVSquad.MaybeCommit

/-! ## State Model -/

/-- Abstract model of the `RaftLog` fields relevant to `maybe_commit`. -/
structure MaybeCommitState where
  /-- Highest log index known to be committed. -/
  committed : Nat
  /-- Highest log index present in the log. -/
  lastIndex : Nat
  /-- Pure model of `self.term(idx)`:  returns `some t` if the log contains
      term `t` at index `idx`, or `none` if the index is out of range or the
      entry is otherwise unavailable. -/
  termFn    : Nat → Option Nat

/-- **WF**: invariants that `RaftLog` maintains.

    * `committed_le_last`  : `committed ≤ lastIndex`
    * `term_le_last`       : every index with a known term is within the log

    The second clause lets us derive `maxIndex ≤ lastIndex` from the guard
    `termFn maxIndex = some term`, matching `commit_to`'s precondition. -/
def MaybeCommitState.WF (s : MaybeCommitState) : Prop :=
  s.committed ≤ s.lastIndex ∧
  ∀ i t, s.termFn i = some t → i ≤ s.lastIndex

/-! ## `maybe_commit` -/

/-- The guard condition of `maybe_commit`:

    `maxIndex > committed  ∧  termFn maxIndex = some term` -/
def maybeCommitCond (s : MaybeCommitState) (maxIndex term : Nat) : Prop :=
  s.committed < maxIndex ∧ s.termFn maxIndex = some term

instance (s : MaybeCommitState) (maxIndex term : Nat) :
    Decidable (maybeCommitCond s maxIndex term) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Model of `RaftLog::maybe_commit`.

    Returns `(new_state, changed)` where `changed = true` iff `committed` advanced. -/
def maybeCommit (s : MaybeCommitState) (maxIndex term : Nat) :
    MaybeCommitState × Bool :=
  if maybeCommitCond s maxIndex term then
    ({ s with committed := maxIndex }, true)
  else
    (s, false)

/-! ## Key properties -/

/-- **PROP-1**: Returns `true` iff the guard condition holds. -/
theorem maybeCommit_true_iff (s : MaybeCommitState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).2 = true ↔ maybeCommitCond s maxIndex term := by
  simp [maybeCommit]

/-- **PROP-2**: Returns `false` iff the guard condition does not hold. -/
theorem maybeCommit_false_iff (s : MaybeCommitState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).2 = false ↔ ¬maybeCommitCond s maxIndex term := by
  simp [maybeCommit]

/-- **PROP-3**: When the condition holds, new `committed = maxIndex`. -/
theorem maybeCommit_committed_eq (s : MaybeCommitState) (maxIndex term : Nat)
    (hcond : maybeCommitCond s maxIndex term) :
    (maybeCommit s maxIndex term).1.committed = maxIndex := by
  simp [maybeCommit, hcond]

/-- **PROP-4**: When the condition does not hold, the state is unchanged. -/
theorem maybeCommit_unchanged (s : MaybeCommitState) (maxIndex term : Nat)
    (hcond : ¬maybeCommitCond s maxIndex term) :
    (maybeCommit s maxIndex term).1 = s := by
  simp [maybeCommit, hcond]

/-- **PROP-5**: `committed` is non-decreasing. -/
theorem maybeCommit_committed_mono (s : MaybeCommitState) (maxIndex term : Nat) :
    s.committed ≤ (maybeCommit s maxIndex term).1.committed := by
  simp only [maybeCommit]
  split_ifs with h
  · simp; exact Nat.le_of_lt h.1
  · simp

/-- **PROP-6**: `committed` strictly advances iff the call returns `true`. -/
theorem maybeCommit_strict_advance_iff (s : MaybeCommitState) (maxIndex term : Nat) :
    s.committed < (maybeCommit s maxIndex term).1.committed ↔
    (maybeCommit s maxIndex term).2 = true := by
  simp only [maybeCommit, maybeCommitCond]
  split_ifs with h
  · simp; exact h.1
  · simp

/-- **PROP-7**: The call returns `true` iff `committed` changed. -/
theorem maybeCommit_changed_iff (s : MaybeCommitState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).1.committed ≠ s.committed ↔
    (maybeCommit s maxIndex term).2 = true := by
  simp only [maybeCommit, maybeCommitCond]
  split_ifs with h
  · simp; exact Nat.ne_of_gt h.1
  · simp

/-- **PROP-8**: If `maxIndex ≤ committed`, the call always returns `false`. -/
theorem maybeCommit_le_committed_false (s : MaybeCommitState) (maxIndex term : Nat)
    (h : maxIndex ≤ s.committed) :
    (maybeCommit s maxIndex term).2 = false := by
  simp [maybeCommit, maybeCommitCond, Nat.not_lt.mpr h]

/-- **PROP-9**: If `termFn maxIndex ≠ some term`, the call always returns `false`. -/
theorem maybeCommit_wrong_term_false (s : MaybeCommitState) (maxIndex term : Nat)
    (h : s.termFn maxIndex ≠ some term) :
    (maybeCommit s maxIndex term).2 = false := by
  simp [maybeCommit, maybeCommitCond, h]

/-- **PROP-10**: `lastIndex` is unchanged by `maybe_commit`. -/
theorem maybeCommit_lastIndex_unchanged (s : MaybeCommitState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).1.lastIndex = s.lastIndex := by
  simp [maybeCommit]
  split_ifs <;> simp

/-- **PROP-11**: `termFn` is unchanged by `maybe_commit`. -/
theorem maybeCommit_termFn_unchanged (s : MaybeCommitState) (maxIndex term : Nat) (j : Nat) :
    (maybeCommit s maxIndex term).1.termFn j = s.termFn j := by
  simp [maybeCommit]
  split_ifs <;> simp

/-- **PROP-12 (WF preservation)**: `maybe_commit` preserves the well-formedness invariant.

    Proof sketch:
    * On success: `committed = maxIndex`.  Since `termFn maxIndex = some term`,
      WF.2 gives `maxIndex ≤ lastIndex`, so the new committed ≤ lastIndex.
      `lastIndex` and `termFn` are unchanged.
    * On failure: state unchanged, WF trivially preserved. -/
theorem maybeCommit_wf (s : MaybeCommitState) (maxIndex term : Nat)
    (hwf : s.WF) :
    (maybeCommit s maxIndex term).1.WF := by
  simp only [maybeCommit, MaybeCommitState.WF]
  split_ifs with hcond
  · constructor
    · -- committed ≤ lastIndex: maxIndex ≤ lastIndex by WF.2 + term check
      exact hwf.2 maxIndex term hcond.2
    · -- term_le_last: termFn unchanged (only committed field updated)
      intro i t ht
      exact hwf.2 i t ht
  · exact hwf

/-- **PROP-13 (idempotent)**: Calling `maybe_commit` again with the same `(maxIndex, term)`
    after a successful call always returns `false`.

    After success, `committed = maxIndex`, so `maxIndex > committed` fails. -/
theorem maybeCommit_idempotent (s : MaybeCommitState) (maxIndex term : Nat)
    (hcond : maybeCommitCond s maxIndex term) :
    (maybeCommit (maybeCommit s maxIndex term).1 maxIndex term).2 = false := by
  simp [maybeCommit, hcond, maybeCommitCond, Nat.lt_irrefl]

/-- **PROP-14**: A successful call is the unique fixed point:
    the returned state differs from the input iff the call returned `true`. -/
theorem maybeCommit_fixed_point (s : MaybeCommitState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).1 = s ↔ ¬maybeCommitCond s maxIndex term := by
  constructor
  · intro heq hcond
    have : (maybeCommit s maxIndex term).1.committed = maxIndex :=
      maybeCommit_committed_eq s maxIndex term hcond
    rw [heq] at this
    exact Nat.not_lt.mpr (Nat.le_of_eq this.symm) hcond.1
  · intro hncond
    exact maybeCommit_unchanged s maxIndex term hncond

/-! ## Composition: two sequential commits -/

/-- **PROP-15**: After a first successful commit to `i₁`, a second commit to `i₂ > i₁`
    (with matching term) also succeeds.

    This models the scenario where the leader first commits at `i₁` then at `i₂`. -/
theorem maybeCommit_sequential (s : MaybeCommitState) (i₁ i₂ t₁ t₂ : Nat)
    (hc1 : maybeCommitCond s i₁ t₁)
    (hgt : i₁ < i₂)
    (hterm : s.termFn i₂ = some t₂) :
    (maybeCommit (maybeCommit s i₁ t₁).1 i₂ t₂).2 = true := by
  rw [maybeCommit_true_iff]
  constructor
  · rw [maybeCommit_committed_eq s i₁ t₁ hc1]; exact hgt
  · rw [maybeCommit_termFn_unchanged]; exact hterm

/-- **PROP-16**: A second `maybe_commit` to the same index is always `false`,
    regardless of whether the first succeeded or failed. -/
theorem maybeCommit_second_same_false (s : MaybeCommitState) (maxIndex term : Nat) :
    (maybeCommit (maybeCommit s maxIndex term).1 maxIndex term).2 = false := by
  by_cases h : maybeCommitCond s maxIndex term
  · -- First call succeeds: committed advances to maxIndex; second guard maxIndex > maxIndex fails
    exact maybeCommit_le_committed_false _ maxIndex term
      (maybeCommit_committed_eq s maxIndex term h ▸ le_refl maxIndex)
  · -- First call fails: state unchanged, same condition still fails
    rw [maybeCommit_unchanged s maxIndex term h]
    exact maybeCommit_false_iff.mpr h

end FVSquad.MaybeCommit
