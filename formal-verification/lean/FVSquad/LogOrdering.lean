/-!
# Log Ordering — Lean 4 Specification

Formal specification of `RaftLog::is_up_to_date` and `RaftLog::find_conflict_by_term`
from `raft-rs` (`src/raft_log.rs`).

## Model scope and approximations

* **Types**: All indices and terms are `Nat` (Rust uses `u64`; overflow not modelled).
* **Log abstraction**: The Raft log is abstracted as `logTerm : Nat → Option Nat`,
  a partial function from index to term. `none` models a compacted (unavailable) entry.
* **`isUpToDate`**: exact functional model of `RaftLog::is_up_to_date`.
* **`findConflictByTerm`**: functional model of the loop in `find_conflict_by_term`;
  uses structural recursion on `index` (decreasing) to guarantee termination.
* **Omitted**: I/O, logging, the `index > last_index` guard (modelled separately as a
  precondition), snapshot/storage interaction, error propagation via `Result`.
* **Dummy-entry assumption**: proofs of safety for `findConflictByTerm` may require
  `logTerm 0 = some 0` (the Raft dummy-entry invariant). This is stated as a hypothesis
  where needed rather than baked in.

🔬 *Lean Squad — auto-generated formal specification.*

-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace FVSquad.LogOrdering

/-! ## `isUpToDate` -/

/-- `isUpToDate selfLastIdx selfLastTerm lastIdx term` models
    `RaftLog::is_up_to_date(last_index, term)`.

    Returns `true` iff the candidate log `(lastIdx, term)` is at least as
    up-to-date as the local log `(selfLastIdx, selfLastTerm)`.

    Raft election restriction (§5.4.1 of the Raft paper):
    - Higher term wins.
    - Equal term: longer log (higher index) wins. -/
def isUpToDate (selfLastIdx selfLastTerm lastIdx term : Nat) : Bool :=
  term > selfLastTerm || (term == selfLastTerm && lastIdx >= selfLastIdx)

/-! ## Sanity checks for `isUpToDate` -/

#eval isUpToDate 5 3 5 3   -- true  (equal logs)
#eval isUpToDate 5 3 4 3   -- false (same term, shorter)
#eval isUpToDate 5 3 4 4   -- true  (higher term wins)
#eval isUpToDate 5 3 6 2   -- false (lower term loses)
#eval isUpToDate 5 3 6 3   -- true  (same term, longer)

/-! ## Theorems about `isUpToDate` -/

/-- Reflexivity: every log is at least as up-to-date as itself. -/
theorem isUpToDate_refl (i t : Nat) : isUpToDate i t i t = true := by
  simp [isUpToDate]

/-- Totality: for any two log positions, at least one is at least as
    up-to-date as the other. -/
theorem isUpToDate_total (i t j s : Nat) :
    isUpToDate i t j s = true ∨ isUpToDate j s i t = true := by
  simp [isUpToDate, Bool.or_eq_true]
  omega

/-- Transitivity: up-to-date is a transitive relation. -/
theorem isUpToDate_trans (i t j s k r : Nat)
    (h1 : isUpToDate i t j s = true)
    (h2 : isUpToDate j s k r = true) :
    isUpToDate i t k r = true := by
  simp [isUpToDate, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at *
  omega

/-- Antisymmetry: mutual up-to-date implies equal log positions. -/
theorem isUpToDate_antisymm (i t j s : Nat)
    (h1 : isUpToDate i t j s = true)
    (h2 : isUpToDate j s i t = true) :
    i = j ∧ t = s := by
  simp [isUpToDate, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at *
  omega

/-- Equivalence to lexicographic order on (term, index).
    `isUpToDate selfI selfT i t ↔ (t, i) ≥ (selfT, selfI)` in lex order. -/
theorem isUpToDate_iff_pair_ge (selfI selfT i t : Nat) :
    isUpToDate selfI selfT i t = true ↔
    (selfT < t ∨ (selfT = t ∧ selfI ≤ i)) := by
  simp [isUpToDate, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq]
  omega

/-- Higher term always gives up-to-date, regardless of index. -/
theorem isUpToDate_higher_term (selfI selfT i t : Nat) (ht : t > selfT) :
    isUpToDate selfI selfT i t = true := by
  simp [isUpToDate, Bool.or_eq_true]
  omega

/-- Same term: up-to-date iff index is at least as large. -/
theorem isUpToDate_same_term (selfI t i : Nat) :
    isUpToDate selfI t i t = true ↔ i ≥ selfI := by
  simp [isUpToDate, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq]
  omega

/-- Lower term never gives up-to-date. -/
theorem isUpToDate_lower_term (selfI selfT i t : Nat) (ht : t < selfT) :
    isUpToDate selfI selfT i t = false := by
  simp [isUpToDate, Bool.or_eq_true]
  omega

/-! ## `findConflictByTerm` -/

/-- Functional model of `RaftLog::find_conflict_by_term`.

    Given a log abstraction `logTerm : Nat → Option Nat` and query `(index, term)`,
    finds the largest `j ≤ index` such that `logTerm j = some t` with `t ≤ term`.
    If `logTerm j = none` (compacted entry), stops and returns `j`.

    Termination: structural recursion on `index`. The Rust loop decrements
    `conflict_index` from `index` toward 0 until the condition is satisfied. -/
def findConflictByTerm (logTerm : Nat → Option Nat) : Nat → Nat → Nat
  | 0,       _    => 0
  | (i + 1), term =>
    match logTerm (i + 1) with
    | none   => i + 1   -- compacted: stop here
    | some t =>
      if t ≤ term then i + 1    -- found: term condition satisfied
      else findConflictByTerm logTerm i term  -- too high: go back one

/-! ## Sanity checks for `findConflictByTerm` -/

-- Log: term at each index is the index itself (t[i] = i)
private def exLog : Nat → Option Nat := fun i => some i

#eval findConflictByTerm exLog 5 3   -- 3 (log[3].term = 3 ≤ 3)
#eval findConflictByTerm exLog 5 2   -- 2 (log[2].term = 2 ≤ 2)
#eval findConflictByTerm exLog 3 3   -- 3
#eval findConflictByTerm exLog 0 3   -- 0

-- Log where all terms are 5 (high), except index 2 has term 1
private def exLog2 : Nat → Option Nat
  | 2 => some 1
  | i => some 5

#eval findConflictByTerm exLog2 5 3   -- 2 (terms at 5,4,3 are 5 > 3; term at 2 is 1 ≤ 3)
#eval findConflictByTerm exLog2 5 6   -- 5 (log[5].term = 5 ≤ 6)

/-! ## Theorems about `findConflictByTerm` -/

/-- The result is always ≤ the input index. -/
theorem findConflictByTerm_le (logTerm : Nat → Option Nat) (index term : Nat) :
    findConflictByTerm logTerm index term ≤ index := by
  induction index with
  | zero => simp [findConflictByTerm]
  | succ n ih =>
    simp [findConflictByTerm]
    split
    · omega
    · rename_i t
      split
      · omega
      · omega

/-- If the term at the result index is available, it satisfies the term condition. -/
theorem findConflictByTerm_term_le (logTerm : Nat → Option Nat) (index term : Nat) :
    ∀ t, logTerm (findConflictByTerm logTerm index term) = some t → t ≤ term := by
  induction index with
  | zero => simp [findConflictByTerm]
  | succ n ih =>
    intro t ht
    simp [findConflictByTerm] at *
    split at ht
    · rename_i heq
      simp [heq] at ht
    · rename_i s heq
      simp [heq] at ht
      split at ht
      · rename_i hle
        simp at ht
        omega
      · rename_i hlt
        exact ih t ht

/-- Monotonicity in index: scanning a larger range gives a result at least
    as large (the scan can go no farther left than a smaller range would). -/
theorem findConflictByTerm_mono_idx (logTerm : Nat → Option Nat) (i j term : Nat)
    (hij : i ≤ j) :
    findConflictByTerm logTerm i term ≤ findConflictByTerm logTerm j term := by
  induction j with
  | zero =>
    simp [findConflictByTerm]
    omega
  | succ n ih =>
    cases Nat.eq_or_lt_of_le hij with
    | inl heq =>
      subst heq
      simp [findConflictByTerm]
      split
      · omega
      · split
        · omega
        · omega
    | inr hlt =>
      have hin : i ≤ n := Nat.lt_succ_iff.mp hlt
      specialize ih hin
      simp [findConflictByTerm]
      split
      · -- logTerm (n+1) = none, result = n+1
        rename_i hne
        calc findConflictByTerm logTerm i term
            ≤ i := findConflictByTerm_le logTerm i term
          _ ≤ n := hin
          _ < n + 1 := Nat.lt_succ_self n
      · rename_i t heq
        split
        · -- logTerm (n+1) = some t, t ≤ term, result = n+1
          calc findConflictByTerm logTerm i term
              ≤ i := findConflictByTerm_le logTerm i term
            _ ≤ n := hin
            _ < n + 1 := Nat.lt_succ_self n
        · -- logTerm (n+1) = some t, t > term, recurse
          exact ih

/-- If `logTerm index = some t` with `t ≤ term`, the result equals `index`
    (no scan needed). -/
theorem findConflictByTerm_found_at_top (logTerm : Nat → Option Nat) (index term t : Nat)
    (heq : logTerm index = some t) (hle : t ≤ term) :
    findConflictByTerm logTerm index term = index := by
  cases index with
  | zero => simp [findConflictByTerm]
  | succ n =>
    simp [findConflictByTerm, heq]
    omega

/-- If `logTerm index = none`, the result equals `index`. -/
theorem findConflictByTerm_none_at_top (logTerm : Nat → Option Nat) (index term : Nat)
    (heq : logTerm index = none) :
    findConflictByTerm logTerm index term = index := by
  cases index with
  | zero => simp [findConflictByTerm]
  | succ n =>
    simp [findConflictByTerm, heq]

/-- The result is 0 when `index = 0`. -/
theorem findConflictByTerm_zero (logTerm : Nat → Option Nat) (term : Nat) :
    findConflictByTerm logTerm 0 term = 0 := by
  simp [findConflictByTerm]

/-- Decreasing term query gives a result ≤ that of a higher term query.
    (A stricter term constraint can only push the result further left.) -/
theorem findConflictByTerm_mono_term (logTerm : Nat → Option Nat) (index t1 t2 : Nat)
    (ht : t1 ≤ t2) :
    findConflictByTerm logTerm index t1 ≤ findConflictByTerm logTerm index t2 := by
  induction index with
  | zero => simp [findConflictByTerm]
  | succ n ih =>
    simp [findConflictByTerm]
    split
    · omega
    · rename_i t heq
      simp only []
      split
      · split
        · omega
        · rename_i hlt
          omega
      · split
        · rename_i hle1 hgt2
          -- t ≤ t1 ≤ t2 and t > t2: contradiction
          omega
        · exact ih

/-! ## Key correctness theorem: all entries above result have term > query term -/

/-- All entries strictly above the result (up to index) have term > the query term.
    This is the key "maximality" property: the result is the *largest* valid index. -/
theorem findConflictByTerm_above_gt (logTerm : Nat → Option Nat) (index term : Nat) :
    ∀ k, findConflictByTerm logTerm index term < k → k ≤ index →
    ∀ t, logTerm k = some t → t > term := by
  induction index with
  | zero =>
    intro k hk hle
    simp [findConflictByTerm] at hk
    omega
  | succ n ih =>
    intro k hk hle t heqt
    simp [findConflictByTerm] at hk
    split at hk
    · -- logTerm (n+1) = none → result = n+1 → k > n+1 but k ≤ n+1: impossible
      rename_i hne
      omega
    · rename_i s hs
      split at hk
      · -- logTerm (n+1) = some s, s ≤ term → result = n+1 → k > n+1: impossible
        omega
      · -- logTerm (n+1) = some s, s > term → recurse
        rename_i hgt
        cases Nat.eq_or_lt_of_le hle with
        | inl heq =>
          -- k = n+1
          have hkn : k = n + 1 := by omega
          subst hkn
          rw [heqt] at hs
          injection hs with hs'
          omega
        | inr hlt =>
          exact ih k hk (Nat.lt_succ_iff.mp hlt) t heqt

end FVSquad.LogOrdering
