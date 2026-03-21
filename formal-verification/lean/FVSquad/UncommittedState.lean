/-!
# UncommittedState — Lean 4 Specification and Implementation Model

Formal specification of `UncommittedState::maybe_increase_uncommitted_size` and
`UncommittedState::maybe_reduce_uncommitted_size` from `raft-rs` (`src/raft.rs`).

`UncommittedState` tracks the total byte size of uncommitted log entries on a **leader**
node, enforcing a configurable budget (`max_uncommitted_size`) on outstanding proposals.
It provides a **"minimum-one-entry" guarantee** (always accept when the queue is empty)
and an **underflow guard** on reduction (clamp to 0 rather than wrapping).

## Operations

| Operation | Semantics |
|-----------|-----------|
| `maybeIncrease s size` | Accept proposal of `size` bytes; return `(s', accepted)` |
| `maybeReduce s size` | Deduct `size` bytes on commit; return `(s', ok)` |

## Model scope and approximations

* **Types**: `usize`/`u64` fields are modelled as `Nat` (no overflow, no 64-bit bound).
  The `NO_LIMIT = u64::MAX` sentinel is captured by `isNoLimit : Bool`.
* **Entry abstraction**: actual `Entry` protobuf values are abstracted to their total
  computed data byte size `size : Nat`. The model does not represent per-entry fields,
  term numbers, or serialisation costs.
* **`filteredSize`**: the Rust `skip_while(e.index ≤ lastLogTailIndex)` filter is modelled
  by `filteredSize`, which uses `List.filter` (set-theoretic). For **sorted** entry lists,
  `dropWhile` and `filter` are equivalent. The sorted-order requirement is a Raft invariant.
* **`lastLogTailIndex`**: included in the struct for completeness; the core size-update
  functions take `size : Nat` directly (the caller passes the result of `filteredSize`).
* **Return types**: Rust `bool` maps to Lean `Bool`. The warning log in the underflow path
  is not modelled.

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas

namespace FVSquad.UncommittedState

/-! ## Types -/

/-- Pure model of `UncommittedState` from `src/raft.rs`. -/
structure UncommittedState where
  /-- Maximum allowed total byte size of uncommitted entries.
      Ignored (effectively unlimited) when `isNoLimit = true`. -/
  maxUncommittedSize : Nat
  /-- Current tracked total uncommitted byte size. -/
  uncommittedSize    : Nat
  /-- True when `max_uncommitted_size = NO_LIMIT (u64::MAX)`. -/
  isNoLimit          : Bool
  /-- Index of last log entry at the moment this node became leader.
      Entries at or below this index are excluded from `filteredSize` calculations. -/
  lastLogTailIndex   : Nat
  deriving DecidableEq, Repr

/-! ## Helper: filteredSize

Models `ents.iter().skip_while(|e| e.index ≤ lastLogTailIndex).map(|e| e.data.len()).sum()`.

Each entry is represented as `(index : Nat, size : Nat)`. We use `List.filter` (set-theoretic
sum over entries with `index > tailIndex`) rather than `dropWhile`, which is equivalent on
sorted lists. -/

/-- Total data size of entries with index strictly greater than `tailIndex`. -/
def filteredSize (tailIndex : Nat) (entries : List (Nat × Nat)) : Nat :=
  (entries.filter (fun e => decide (tailIndex < e.1))).map Prod.snd |>.sum

/-! ## Implementation model -/

/-- Boolean acceptance condition for `maybeIncrease`:
    true iff the batch should be accepted (size = 0, queue empty, or within budget). -/
private def increaseCond (s : UncommittedState) (size : Nat) : Bool :=
  (size == 0) || (s.uncommittedSize == 0) ||
  decide (size + s.uncommittedSize ≤ s.maxUncommittedSize)

/-- Model of `maybe_increase_uncommitted_size`. Returns `(new_state, accepted)`.
    - `isNoLimit` fast path: always accept, no state change.
    - Otherwise: accept iff `size = 0`, `uncommittedSize = 0`, or within budget. -/
def maybeIncrease (s : UncommittedState) (size : Nat) : UncommittedState × Bool :=
  if s.isNoLimit then
    (s, true)
  else if increaseCond s size then
    ({ s with uncommittedSize := s.uncommittedSize + size }, true)
  else
    (s, false)

/-- Model of `maybe_reduce_uncommitted_size`. Returns `(new_state, ok)`.
    - `isNoLimit` fast path: always ok, no state change.
    - Underflow guard: if `size > uncommittedSize`, clamp to 0, return false.
    - Otherwise: subtract `size`, return true. -/
def maybeReduce (s : UncommittedState) (size : Nat) : UncommittedState × Bool :=
  if s.isNoLimit then
    (s, true)
  else if s.uncommittedSize < size then
    ({ s with uncommittedSize := 0 }, false)
  else
    ({ s with uncommittedSize := s.uncommittedSize - size }, true)

/-! ## Sanity checks via `native_decide` -/

-- Rejection: S=900, M=1000, size=200 → rejected (900 + 200 > 1000)
example : maybeIncrease ⟨1000, 900, false, 5⟩ 200 =
    (⟨1000, 900, false, 5⟩, false) := by native_decide

-- Acceptance within budget: S=100, M=1000, size=50 → accepted
example : maybeIncrease ⟨1000, 100, false, 5⟩ 50 =
    (⟨1000, 150, false, 5⟩, true) := by native_decide

-- One-entry guarantee: S=0, M=100, size=500 → accepted even over limit
example : maybeIncrease ⟨100, 0, false, 5⟩ 500 =
    (⟨100, 500, false, 5⟩, true) := by native_decide

-- Empty entry (size=0): always accepted
example : maybeIncrease ⟨100, 50, false, 5⟩ 0 =
    (⟨100, 50, false, 5⟩, true) := by native_decide

-- isNoLimit fast path: state unchanged, always accepted
example : maybeIncrease ⟨100, 50, true, 5⟩ 999 =
    (⟨100, 50, true, 5⟩, true) := by native_decide

-- Normal reduce: S=150, size=50 → S_new=100
example : maybeReduce ⟨1000, 150, false, 5⟩ 50 =
    (⟨1000, 100, false, 5⟩, true) := by native_decide

-- Underflow: S=20, size=50 → S_new=0, false
example : maybeReduce ⟨1000, 20, false, 5⟩ 50 =
    (⟨1000, 0, false, 5⟩, false) := by native_decide

-- filteredSize: entries before tail are excluded
example : filteredSize 5 [(3, 10), (5, 20), (6, 30), (8, 40)] = 70 := by native_decide

-- filteredSize: all entries before tail → 0
example : filteredSize 10 [(1, 5), (7, 8), (10, 3)] = 0 := by native_decide

/-! ## Lemma: increaseCond characterisation -/

private lemma increaseCond_iff (s : UncommittedState) (size : Nat) :
    increaseCond s size = true ↔
    (size = 0 ∨ s.uncommittedSize = 0 ∨ size + s.uncommittedSize ≤ s.maxUncommittedSize) := by
  simp [increaseCond, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]

/-! ## Lemmas about `filteredSize` -/

@[simp] theorem filteredSize_nil (t : Nat) : filteredSize t [] = 0 := by
  simp [filteredSize]

/-- All entries at or before `tailIndex` contribute zero to `filteredSize`. -/
theorem filteredSize_all_old (t : Nat) (entries : List (Nat × Nat))
    (h : ∀ e ∈ entries, e.1 ≤ t) : filteredSize t entries = 0 := by
  induction entries with
  | nil => simp [filteredSize]
  | cons hd tl ih =>
    simp only [filteredSize, List.filter, List.map, List.sum_cons]
    have hhd : ¬(t < hd.1) := Nat.not_lt.mpr (h hd (List.mem_cons_self _ _))
    simp only [decide_eq_true_eq, hhd, not_false_eq_true, decide_false, List.filter]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- A head entry at or before `tailIndex` is excluded from `filteredSize`. -/
theorem filteredSize_cons_old (t i sz : Nat) (rest : List (Nat × Nat))
    (hi : i ≤ t) : filteredSize t ((i, sz) :: rest) = filteredSize t rest := by
  simp [filteredSize, decide_eq_false_iff_not.mpr (Nat.not_lt.mpr hi)]

/-- A head entry strictly after `tailIndex` is included. -/
theorem filteredSize_cons_new (t i sz : Nat) (rest : List (Nat × Nat))
    (hi : t < i) : filteredSize t ((i, sz) :: rest) = sz + filteredSize t rest := by
  simp [filteredSize, decide_eq_true_eq.mpr hi]

/-! ## Theorems about `maybeIncrease` -/

/-- `isNoLimit` fast path: result is `(s, true)` with no state change. -/
theorem increase_noLimit_result (s : UncommittedState) (size : Nat)
    (h : s.isNoLimit = true) : maybeIncrease s size = (s, true) := by
  simp [maybeIncrease, h]

/-- `isNoLimit` fast path always returns `true`. -/
theorem increase_noLimit_true (s : UncommittedState) (size : Nat)
    (h : s.isNoLimit = true) : (maybeIncrease s size).2 = true :=
  increase_noLimit_result s size h ▸ rfl

/-- `isNoLimit` fast path leaves state unchanged. -/
theorem increase_noLimit_unchanged (s : UncommittedState) (size : Nat)
    (h : s.isNoLimit = true) : (maybeIncrease s size).1 = s :=
  increase_noLimit_result s size h ▸ rfl

/-- Empty entries (`size = 0`) are always accepted. -/
theorem increase_zero_accepted (s : UncommittedState)
    (hn : s.isNoLimit = false) : (maybeIncrease s 0).2 = true := by
  simp [maybeIncrease, hn, increaseCond]

/-- **At-least-one-entry guarantee**: when `uncommittedSize = 0`, any batch is accepted. -/
theorem increase_empty_state_accepted (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false) (hs : s.uncommittedSize = 0) :
    (maybeIncrease s size).2 = true := by
  simp [maybeIncrease, hn, increaseCond, hs]

/-- Within-budget proposals are accepted. -/
theorem increase_within_budget_accepted (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false)
    (hb : size + s.uncommittedSize ≤ s.maxUncommittedSize) :
    (maybeIncrease s size).2 = true := by
  simp [maybeIncrease, hn, increaseCond, decide_eq_true_eq.mpr hb]

/-- **Exact characterisation** of acceptance (when `isNoLimit = false`). -/
theorem increase_true_iff (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false) :
    (maybeIncrease s size).2 = true ↔
    (size = 0 ∨ s.uncommittedSize = 0 ∨ size + s.uncommittedSize ≤ s.maxUncommittedSize) := by
  rw [show (maybeIncrease s size).2 = increaseCond s size from ?_]
  · exact increaseCond_iff s size
  · simp only [maybeIncrease, hn, if_false]
    split_ifs with hc <;> simp [hc]

/-- **Rejection is non-mutating**: when `accepted = false`, state is unchanged. -/
theorem increase_false_unchanged (s : UncommittedState) (size : Nat)
    (h : (maybeIncrease s size).2 = false) :
    (maybeIncrease s size).1 = s := by
  simp only [maybeIncrease] at *
  split_ifs at h ⊢ with hL hC
  · simp at h
  · simp at h
  · rfl

/-- **Acceptance updates size**: accepted proposals add exactly `size` bytes. -/
theorem increase_true_size (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false) (h : (maybeIncrease s size).2 = true) :
    (maybeIncrease s size).1.uncommittedSize = s.uncommittedSize + size := by
  simp only [maybeIncrease, hn, if_false] at *
  split_ifs at h ⊢ with hC
  · rfl
  · simp at h

/-- **Budget invariant**: accepting a non-trivial proposal (size ≠ 0, state ≠ 0)
    ensures `new_uncommittedSize ≤ maxUncommittedSize`. -/
theorem increase_budget (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false)
    (hS : s.uncommittedSize ≠ 0)
    (hSz : size ≠ 0)
    (h : (maybeIncrease s size).2 = true) :
    (maybeIncrease s size).1.uncommittedSize ≤ s.maxUncommittedSize := by
  rw [increase_true_size s size hn h]
  rw [increase_true_iff s size hn] at h
  rcases h with h | h | h
  · exact absurd h hSz
  · exact absurd h hS
  · omega

/-- `isNoLimit` is preserved by `maybeIncrease`. -/
theorem increase_isNoLimit_preserved (s : UncommittedState) (size : Nat) :
    (maybeIncrease s size).1.isNoLimit = s.isNoLimit := by
  simp only [maybeIncrease]
  split_ifs <;> simp

/-! ## Theorems about `maybeReduce` -/

/-- `isNoLimit` fast path: result is `(s, true)` with no state change. -/
theorem reduce_noLimit_result (s : UncommittedState) (size : Nat)
    (h : s.isNoLimit = true) : maybeReduce s size = (s, true) := by
  simp [maybeReduce, h]

/-- `isNoLimit` fast path always returns `true`. -/
theorem reduce_noLimit_true (s : UncommittedState) (size : Nat)
    (h : s.isNoLimit = true) : (maybeReduce s size).2 = true :=
  reduce_noLimit_result s size h ▸ rfl

/-- `isNoLimit` fast path leaves state unchanged. -/
theorem reduce_noLimit_unchanged (s : UncommittedState) (size : Nat)
    (h : s.isNoLimit = true) : (maybeReduce s size).1 = s :=
  reduce_noLimit_result s size h ▸ rfl

/-- Zero-size reduction is always `(s, true)`. -/
theorem reduce_zero_noop (s : UncommittedState) (hn : s.isNoLimit = false) :
    maybeReduce s 0 = (s, true) := by
  simp [maybeReduce, hn]

/-- **Underflow guard**: when `size > uncommittedSize`, state is clamped to 0 and returns false. -/
theorem reduce_underflow (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false)
    (h : size > s.uncommittedSize) :
    (maybeReduce s size).1.uncommittedSize = 0 ∧ (maybeReduce s size).2 = false := by
  simp only [maybeReduce, hn, if_false]
  rw [if_pos h]
  exact ⟨rfl, rfl⟩

/-- **Normal reduction**: when `size ≤ uncommittedSize`, subtracts and returns true. -/
theorem reduce_normal (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false)
    (h : size ≤ s.uncommittedSize) :
    (maybeReduce s size).1.uncommittedSize = s.uncommittedSize - size ∧
    (maybeReduce s size).2 = true := by
  simp only [maybeReduce, hn, if_false]
  rw [if_neg (Nat.not_lt.mpr h)]
  exact ⟨rfl, rfl⟩

/-- **Monotone decrease**: `maybeReduce` never increases `uncommittedSize`. -/
theorem reduce_monotone (s : UncommittedState) (size : Nat) :
    (maybeReduce s size).1.uncommittedSize ≤ s.uncommittedSize := by
  simp only [maybeReduce]
  split_ifs with hL hU
  · -- isNoLimit fast path
    simp
  · -- underflow: new size = 0 ≤ s.uncommittedSize
    simp; omega
  · -- normal: s.uncommittedSize - size ≤ s.uncommittedSize
    simp; omega

/-- **Exact characterisation** of `true` return (when `isNoLimit = false`). -/
theorem reduce_true_iff (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false) :
    (maybeReduce s size).2 = true ↔ size ≤ s.uncommittedSize := by
  simp only [maybeReduce, hn, if_false]
  split_ifs with hU
  · -- underflow case: hU : s.uncommittedSize < size
    simp only [Bool.false_eq_true, false_iff]
    exact Nat.not_le.mpr hU
  · -- normal case
    simp only [true_iff]
    exact Nat.le_of_not_lt hU

/-- `isNoLimit` is preserved by `maybeReduce`. -/
theorem reduce_isNoLimit_preserved (s : UncommittedState) (size : Nat) :
    (maybeReduce s size).1.isNoLimit = s.isNoLimit := by
  simp only [maybeReduce]
  split_ifs <;> simp

/-! ## Combined: round-trip theorems -/

/-- **Round-trip identity**: increasing then reducing by the same `size` recovers
    the original `uncommittedSize`. Requires acceptance and no-limit = false. -/
theorem increase_reduce_roundtrip (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false)
    (hAccept : (maybeIncrease s size).2 = true) :
    (maybeReduce (maybeIncrease s size).1 size).1.uncommittedSize = s.uncommittedSize := by
  have hNewSize := increase_true_size s size hn hAccept
  have hNL : (maybeIncrease s size).1.isNoLimit = false := by
    rw [increase_isNoLimit_preserved]; exact hn
  simp only [maybeReduce, hNL, if_false]
  -- The underflow check: is (s.uncommittedSize + size) < size?  No: omega.
  rw [if_neg (by rw [hNewSize]; omega)]
  rw [hNewSize]; omega

/-- **Round-trip ok**: the reduce after increase returns `true`. -/
theorem increase_reduce_roundtrip_ok (s : UncommittedState) (size : Nat)
    (hn : s.isNoLimit = false)
    (hAccept : (maybeIncrease s size).2 = true) :
    (maybeReduce (maybeIncrease s size).1 size).2 = true := by
  rw [reduce_true_iff _ _ (by rw [increase_isNoLimit_preserved]; exact hn)]
  rw [increase_true_size s size hn hAccept]
  omega

/-- Successive reductions are also monotone: applying two reductions reduces further. -/
theorem reduce_twice_monotone (s : UncommittedState) (a b : Nat) :
    (maybeReduce (maybeReduce s a).1 b).1.uncommittedSize ≤ s.uncommittedSize := by
  calc (maybeReduce (maybeReduce s a).1 b).1.uncommittedSize
      ≤ (maybeReduce s a).1.uncommittedSize := reduce_monotone _ b
    _ ≤ s.uncommittedSize                  := reduce_monotone s a

end FVSquad.UncommittedState
