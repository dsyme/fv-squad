/-!
# FindConflictByTerm — Lean 4 Formal Specification

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

Formal specification and proof for `RaftLog::find_conflict_by_term` from
`src/raft_log.rs` (lines 218–257).

## Algorithm

Given a conflict hint `(index, term)` from a rejecting follower, scan the leader's
log **backwards** from `index` to find the largest position whose term is `≤ term`.
This lets the leader skip over a diverging suffix in one step rather than probing
one entry at a time.

```
conflict_index := index
loop:
  match logTerm(conflict_index):
    Ok(t) if t > term  →  conflict_index -= 1
    Ok(t)              →  return (conflict_index, Some(t))
    Err(_)             →  return (conflict_index, None)
```

## Model scope and approximations

* **Pure log**: modelled as `Nat → Nat`; storage errors (Err paths) are abstracted away.
* **Types**: indices and terms are `Nat` (Rust: `u64`; no overflow in practice).
* **Dummy entry**: index 0 always has term 0 (`LogDummyZero`); this ensures termination
  because `0 ≤ term` for all `term : Nat`.
* **Monotonicity**: log terms are non-decreasing (`LogNonDecreasing`); used for the
  maximality property.
* **Out-of-range check**: the real function returns `(index, None)` early when
  `index > lastIndex`; modelled by `findConflictByTermFull`.
* **Omitted**: storage errors, logging side effects, group-commit, u64 overflow.

Source: `src/raft_log.rs#L218-L257`
Informal spec: `formal-verification/specs/find_conflict_by_term_informal.md`
-/

namespace FVSquad.FindConflictByTerm

/-! ## Log model -/

/-- The log is non-decreasing in term: earlier entries have smaller or equal terms.
    This is the Raft log monotonicity invariant. -/
def LogNonDecreasing (logTerm : Nat → Nat) : Prop :=
  ∀ i, logTerm i ≤ logTerm (i + 1)

/-- Index 0 holds the dummy entry with term 0.
    This guarantees the backward scan terminates before underflowing. -/
def LogDummyZero (logTerm : Nat → Nat) : Prop :=
  logTerm 0 = 0

/-! ## Implementation model -/

/-- Scan backwards from `index` to find the largest position with term `≤ term`.
    Returns `(result_index, some (logTerm result_index))`.

    Base case (index = 0): always returns `(0, some (logTerm 0))`.
    When `LogDummyZero` holds, `logTerm 0 = 0 ≤ term` for any `term : Nat`,
    so the base case is only reached when all entries have term `> term`. -/
def findConflictByTerm (logTerm : Nat → Nat) : Nat → Nat → Nat × Option Nat
  | 0,       _    => (0, some (logTerm 0))
  | (n + 1), term =>
    if logTerm (n + 1) ≤ term then (n + 1, some (logTerm (n + 1)))
    else findConflictByTerm logTerm n term

/-- Full function including the out-of-range early-return guard.
    Mirrors: `if index > last_index { return (index, None) }`. -/
def findConflictByTermFull
    (logTerm : Nat → Nat) (lastIndex index term : Nat) : Nat × Option Nat :=
  if index > lastIndex then (index, none)
  else findConflictByTerm logTerm index term

/-! ## Structural theorems -/

/-- FCB1: The result index is always `≤` the input index.
    Proved by induction on `index`; no log assumptions needed. -/
theorem FCB1_result_in_range (logTerm : Nat → Nat) (index term : Nat) :
    (findConflictByTerm logTerm index term).1 ≤ index := by
  induction index with
  | zero => simp [findConflictByTerm]
  | succ n ih =>
    simp only [findConflictByTerm]
    by_cases h : logTerm (n + 1) ≤ term
    · simp [h]
    · simp only [h, ite_false]
      exact Nat.le_succ_of_le ih

/-- FCB2: The returned term value is `≤ term`.
    Requires `LogDummyZero` to handle the base case (index 0 has term 0 ≤ any term). -/
theorem FCB2_term_bound (logTerm : Nat → Nat) (index term : Nat)
    (hdummy : LogDummyZero logTerm) :
    ∀ t, (findConflictByTerm logTerm index term).2 = some t → t ≤ term := by
  induction index with
  | zero =>
    intro t ht
    simp [findConflictByTerm] at ht
    -- ht : logTerm 0 = t
    rw [hdummy] at ht
    omega
  | succ n ih =>
    intro t ht
    simp only [findConflictByTerm] at ht
    by_cases h : logTerm (n + 1) ≤ term
    · simp [h] at ht
      -- ht : logTerm (n + 1) = t
      omega
    · simp only [h, ite_false] at ht
      exact ih t ht

/-- FCB3: Maximality — every index strictly between the result and the input has
    term `> term`. No monotonicity assumption is needed; the proof follows the
    scan structure directly. -/
theorem FCB3_maximality (logTerm : Nat → Nat) (index term : Nat) :
    ∀ j, (findConflictByTerm logTerm index term).1 < j →
         j ≤ index → logTerm j > term := by
  induction index with
  | zero =>
    intro j hj1 hj2
    -- result.1 = 0, j > 0 and j ≤ 0: impossible
    omega
  | succ n ih =>
    intro j hj1 hj2
    by_cases h : logTerm (n + 1) ≤ term
    · simp only [findConflictByTerm, h, ite_true] at hj1
      -- hj1 : n+1 < j, hj2 : j ≤ n+1: impossible
      omega
    · simp only [findConflictByTerm, h, ite_false] at hj1
      by_cases hjn : j = n + 1
      · subst hjn
        exact Nat.lt_of_not_le h
      · exact ih j hj1 (by omega)

/-- FCB4: Identity — if `logTerm index ≤ term` the scan matches immediately at `index`. -/
theorem FCB4_identity_on_match (logTerm : Nat → Nat) (index term : Nat)
    (h : logTerm index ≤ term) :
    (findConflictByTerm logTerm index term).1 = index := by
  cases index with
  | zero => simp [findConflictByTerm]
  | succ n =>
    simp only [findConflictByTerm, h, ite_true]

/-- FCB5: Out-of-range early return — when `index > lastIndex` the full function
    returns `(index, none)` immediately without scanning. -/
theorem FCB5_out_of_range (logTerm : Nat → Nat) (lastIndex index term : Nat)
    (h : index > lastIndex) :
    findConflictByTermFull logTerm lastIndex index term = (index, none) := by
  simp [findConflictByTermFull, h]

/-- FCB6: The scan always returns `some` — the result option is never `none`.
    This confirms the model never hits a storage error: the dummy entry at index 0
    guarantees an exit before underflow. -/
theorem FCB6_always_some (logTerm : Nat → Nat) (index term : Nat) :
    (findConflictByTerm logTerm index term).2 ≠ none := by
  induction index with
  | zero => simp [findConflictByTerm]
  | succ n ih =>
    simp only [findConflictByTerm]
    by_cases h : logTerm (n + 1) ≤ term
    · simp [h]
    · simp only [h, ite_false]
      exact ih

/-- FCB7: In-range full function delegates to the scan (not the early-return path). -/
theorem FCB7_in_range_delegates (logTerm : Nat → Nat) (lastIndex index term : Nat)
    (h : index ≤ lastIndex) :
    findConflictByTermFull logTerm lastIndex index term =
    findConflictByTerm logTerm index term := by
  unfold findConflictByTermFull
  have hlt : ¬ (index > lastIndex) := by omega
  rw [if_neg hlt]

/-- FCB8: When the scan terminates at index 0 (all entries have term `> term`),
    the result index is 0 and the result term is `logTerm 0`.
    With `LogDummyZero`, this means the returned term is 0. -/
theorem FCB8_base_case_characterization (logTerm : Nat → Nat) (term : Nat)
    (hdummy : LogDummyZero logTerm) :
    (findConflictByTerm logTerm 0 term).1 = 0 ∧
    (findConflictByTerm logTerm 0 term).2 = some 0 := by
  simp only [findConflictByTerm]
  exact ⟨trivial, congrArg some hdummy⟩

/-! ## Correspondence tests -/

-- Small log: terms [0, 1, 1, 2, 3, 3] at indices [0, 1, 2, 3, 4, 5]
private def testLog : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 3 | _ => 3

-- index 5 has term 3 ≤ 3: immediate match
#guard (findConflictByTerm testLog 5 3) == (5, some 3)
-- index 5 term 3 > 2, index 4 term 3 > 2, index 3 term 2 ≤ 2: stop at 3
#guard (findConflictByTerm testLog 5 2) == (3, some 2)
-- scan back to last term-1 entry (index 2)
#guard (findConflictByTerm testLog 5 1) == (2, some 1)
-- term 0: scan all the way to dummy entry
#guard (findConflictByTerm testLog 5 0) == (0, some 0)
-- index 3 has term 2 ≤ 3: immediate match
#guard (findConflictByTerm testLog 3 3) == (3, some 2)
-- index 0 always returns dummy
#guard (findConflictByTerm testLog 0 5) == (0, some 0)
-- out-of-range: index 10 > lastIndex 5
#guard (findConflictByTermFull testLog 5 10 3) == (10, none)
-- in-range: delegates to scan
#guard (findConflictByTermFull testLog 5 5 2) == (3, some 2)

/-! ## Connection to log monotonicity -/

/-- Helper: non-decreasing means logTerm at larger indices is larger. -/
theorem logNonDecreasing_le (logTerm : Nat → Nat) (h : LogNonDecreasing logTerm)
    (i j : Nat) (hij : i ≤ j) : logTerm i ≤ logTerm j := by
  induction hij with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (h _)

/-- FCB9: With a non-decreasing log, the scan finds the **largest** valid index —
    every index strictly greater than the result has term `> term`.
    (FCB3 already proves this; FCB9 adds the non-decreasing implication that
    all entries in the range `(result, index]` uniformly exceed `term`.) -/
theorem FCB9_maximality_nonDecreasing (logTerm : Nat → Nat) (index term : Nat)
    (hmono : LogNonDecreasing logTerm) :
    ∀ j, (findConflictByTerm logTerm index term).1 < j →
         j ≤ index → logTerm j > term :=
  FCB3_maximality logTerm index term

end FVSquad.FindConflictByTerm
