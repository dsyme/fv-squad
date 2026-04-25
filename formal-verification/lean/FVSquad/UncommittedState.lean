/-!
# UncommittedState — Model and Proofs for Flow-Control Byte Accounting

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: `src/raft.rs` — struct `UncommittedState` and its two mutating methods.

`UncommittedState` implements **flow control** for a Raft leader: it tracks the
total byte-size of log entries proposed but not yet committed and enforces an optional
upper bound (`maxUncommittedSize`) on that total.  A value of `maxUncommittedSize = 0`
means "no limit" (the `NO_LIMIT` sentinel).

## Modelling Choices

We model entries as `List Nat` where each element is the byte-size of one entry.
The `last_log_tail_index` filter is modelled by receiving a pre-filtered `size`
directly.  Lean `Nat.sub` saturates at 0, matching the Rust set-to-zero branch.

## Theorem Index

| ID   | Name                                     | Status    | Description                                                    |
|------|------------------------------------------|-----------|----------------------------------------------------------------|
| US1  | `isNoLimit_increase_true`                | ✅ proved | `max = 0` ⟹ `maybeIncrease` always returns `true`             |
| US2  | `isNoLimit_reduce_true`                  | ✅ proved | `noLimit = true` ⟹ `maybeReduce` always returns `true`        |
| US3  | `emptyEntries_increase_true`             | ✅ proved | `size = 0` ⟹ `maybeIncrease` always returns `true`            |
| US4  | `zeroUncommitted_increase_true`          | ✅ proved | `uncommittedSize = 0` ⟹ `maybeIncrease` always returns `true` |
| US5  | `maybeIncrease_true_effect`              | ✅ proved | allowed ⟹ `uncommittedSize` increases by `size`               |
| US6  | `maybeIncrease_false_nochange`           | ✅ proved | rejected ⟹ `uncommittedSize` unchanged                        |
| US7  | `maybeIncrease_within_budget_true`       | ✅ proved | `size + uncommittedSize ≤ max` ⟹ returns `true`               |
| US8  | `maybeReduce_true_effect`                | ✅ proved | normal reduce ⟹ `uncommittedSize` decreases by `size`         |
| US9  | `maybeReduce_false_zero`                 | ✅ proved | overflow reduce ⟹ `uncommittedSize` set to 0                  |
| US10 | `maybeReduce_nonneg`                     | ✅ proved | `uncommittedSize` never goes negative                         |
| US11 | `maybeIncrease_bounded`                  | ✅ proved | INV1 (`max ≠ 0`): within bound before ⟹ within bound after   |
| US12 | `maybeReduce_le_before`                  | ✅ proved | reduce never increases `uncommittedSize`                       |
| US13 | `maybeIncrease_roundtrip`                | ✅ proved | increase then reduce with same size restores `uncommittedSize` |
| US14 | `emptyList_reduce_noop`                  | ✅ proved | `size = 0` ⟹ `maybeReduce` is a no-op                         |
| US15 | `maybeIncrease_size_zero_unchanged`      | ✅ proved | `size = 0` ⟹ `maybeIncrease` leaves `uncommittedSize` same    |
| US16 | `maybeIncrease_false_iff`                | ✅ proved | Complete rejection iff: max≠0 ∧ size≠0 ∧ used≠0 ∧ over-budget |
| US17 | `maybeIncrease_true_iff`                 | ✅ proved | Complete acceptance iff: max=0 ∨ size=0 ∨ used=0 ∨ fits (dual US16) |
| US18 | `maybeReduce_ge_sub`                     | ✅ proved | reduce: `uncommittedSize - size ≤ result` (saturation safety)  |

**Sorry count**: 0.  All theorems are proved without `sorry`.
-/

namespace FVSquad.UncommittedState

/-! ## Types and definitions -/

structure US where
  maxUncommittedSize : Nat
  uncommittedSize    : Nat
  deriving Repr, DecidableEq

def maybeIncrease (s : US) (size : Nat) : US × Bool :=
  if s.maxUncommittedSize = 0 then
    ({ s with uncommittedSize := s.uncommittedSize + size }, true)
  else if size = 0 then
    ({ s with uncommittedSize := s.uncommittedSize + size }, true)
  else if s.uncommittedSize = 0 then
    ({ s with uncommittedSize := s.uncommittedSize + size }, true)
  else if size + s.uncommittedSize ≤ s.maxUncommittedSize then
    ({ s with uncommittedSize := s.uncommittedSize + size }, true)
  else
    (s, false)

def maybeReduce (s : US) (noLimit : Bool) (size : Nat) : US × Bool :=
  if noLimit then
    (s, true)
  else if size = 0 then
    (s, true)
  else if size > s.uncommittedSize then
    ({ s with uncommittedSize := 0 }, false)
  else
    ({ s with uncommittedSize := s.uncommittedSize - size }, true)

/-! ## Proofs -/

/-- **US1** — `max = 0` ⟹ `maybeIncrease` always returns `true`. -/
theorem US1_isNoLimit_increase_true (s : US) (size : Nat)
    (hno : s.maxUncommittedSize = 0) :
    (maybeIncrease s size).2 = true := by
  simp [maybeIncrease, hno]

/-- **US2** — `noLimit = true` ⟹ `maybeReduce` always returns `true`. -/
theorem US2_isNoLimit_reduce_true (s : US) (size : Nat) :
    (maybeReduce s true size).2 = true := by
  simp [maybeReduce]

/-- **US3** — `size = 0` ⟹ `maybeIncrease` always returns `true`. -/
theorem US3_emptyEntries_increase_true (s : US) :
    (maybeIncrease s 0).2 = true := by
  simp [maybeIncrease]

/-- **US4** — `uncommittedSize = 0` ⟹ `maybeIncrease` always returns `true`. -/
theorem US4_zeroUncommitted_increase_true (s : US) (size : Nat)
    (hz : s.uncommittedSize = 0) :
    (maybeIncrease s size).2 = true := by
  simp [maybeIncrease, hz]

/-- **US5** — `maybeIncrease` returns `true` ⟹ `uncommittedSize` increases by `size`. -/
theorem US5_maybeIncrease_true_effect (s : US) (size : Nat)
    (h : (maybeIncrease s size).2 = true) :
    (maybeIncrease s size).1.uncommittedSize = s.uncommittedSize + size := by
  unfold maybeIncrease at h ⊢
  by_cases hno : s.maxUncommittedSize = 0
  · simp [hno]
  · simp only [if_neg hno] at h ⊢
    by_cases hzs : size = 0
    · simp [hzs]
    · simp only [if_neg hzs] at h ⊢
      by_cases hzu : s.uncommittedSize = 0
      · simp [hzu]
      · simp only [if_neg hzu] at h ⊢
        by_cases hbud : size + s.uncommittedSize ≤ s.maxUncommittedSize
        · simp [hbud]
        · simp [hbud] at h

/-- **US6** — `maybeIncrease` returns `false` ⟹ state unchanged. -/
theorem US6_maybeIncrease_false_nochange (s : US) (size : Nat)
    (h : (maybeIncrease s size).2 = false) :
    (maybeIncrease s size).1 = s := by
  unfold maybeIncrease at h ⊢
  by_cases hno : s.maxUncommittedSize = 0
  · simp [hno] at h
  · simp only [if_neg hno] at h ⊢
    by_cases hzs : size = 0
    · simp [hzs] at h
    · simp only [if_neg hzs] at h ⊢
      by_cases hzu : s.uncommittedSize = 0
      · simp [hzu] at h
      · simp only [if_neg hzu] at h ⊢
        by_cases hbud : size + s.uncommittedSize ≤ s.maxUncommittedSize
        · simp [hbud] at h
        · simp [hbud]

/-- **US7** — `size + uncommittedSize ≤ max` ⟹ `maybeIncrease` returns `true`. -/
theorem US7_maybeIncrease_within_budget_true (s : US) (size : Nat)
    (hbud : size + s.uncommittedSize ≤ s.maxUncommittedSize) :
    (maybeIncrease s size).2 = true := by
  unfold maybeIncrease
  by_cases hno : s.maxUncommittedSize = 0
  · simp [hno]
  · simp only [if_neg hno]
    by_cases hzs : size = 0
    · simp [hzs]
    · simp only [if_neg hzs]
      by_cases hzu : s.uncommittedSize = 0
      · simp [hzu]
      · simp [hzu, hbud]

/-- **US8** — `maybeReduce` returns `true` (with `noLimit = false`) ⟹
    `uncommittedSize` decreases by `size`. -/
theorem US8_maybeReduce_true_effect (s : US) (size : Nat)
    (hret : (maybeReduce s false size).2 = true) :
    (maybeReduce s false size).1.uncommittedSize = s.uncommittedSize - size := by
  simp only [maybeReduce, Bool.false_eq_true, if_false] at hret ⊢
  by_cases hzs : size = 0
  · simp [hzs]
  · simp only [if_neg hzs] at hret ⊢
    by_cases hgt : size > s.uncommittedSize
    · simp [hgt] at hret
    · simp [hgt]

/-- **US9** — `maybeReduce` returns `false` ⟹ `uncommittedSize` set to 0. -/
theorem US9_maybeReduce_false_zero (s : US) (noLimit : Bool) (size : Nat)
    (hret : (maybeReduce s noLimit size).2 = false) :
    (maybeReduce s noLimit size).1.uncommittedSize = 0 := by
  unfold maybeReduce at hret ⊢
  by_cases hno : noLimit
  · simp [hno] at hret
  · simp only [if_neg hno] at hret ⊢
    by_cases hzs : size = 0
    · simp [hzs] at hret
    · simp only [if_neg hzs] at hret ⊢
      by_cases hgt : size > s.uncommittedSize
      · simp [hgt]
      · simp [hgt] at hret

/-- **US10** — `uncommittedSize` never goes negative (Nat saturation). -/
theorem US10_maybeReduce_nonneg (s : US) (noLimit : Bool) (size : Nat) :
    0 ≤ (maybeReduce s noLimit size).1.uncommittedSize := Nat.zero_le _

/-- **US11** — INV1: if `max ≠ 0`, `uncommittedSize ≠ 0` (no starvation-prevention path),
    `uncommittedSize ≤ max` before, and `maybeIncrease` succeeds, then
    `uncommittedSize ≤ max` after.

    Note: when `uncommittedSize = 0`, `maybeIncrease` always accepts (starvation
    prevention) and may exceed `max`; that case is excluded by `hnzu`. -/
theorem US11_maybeIncrease_bounded (s : US) (size : Nat)
    (hno  : s.maxUncommittedSize ≠ 0)
    (hnzu : s.uncommittedSize ≠ 0)
    (hinv : s.uncommittedSize ≤ s.maxUncommittedSize)
    (hok  : (maybeIncrease s size).2 = true) :
    (maybeIncrease s size).1.uncommittedSize ≤ s.maxUncommittedSize := by
  have heff := US5_maybeIncrease_true_effect s size hok
  rw [heff]
  unfold maybeIncrease at hok
  simp only [if_neg hno] at hok
  by_cases hzs : size = 0
  · omega
  · simp only [if_neg hzs, if_neg hnzu] at hok
    by_cases hbud : size + s.uncommittedSize ≤ s.maxUncommittedSize
    · omega
    · simp [hbud] at hok

/-- **US12** — `maybeReduce` never increases `uncommittedSize`. -/
theorem US12_maybeReduce_le_before (s : US) (noLimit : Bool) (size : Nat) :
    (maybeReduce s noLimit size).1.uncommittedSize ≤ s.uncommittedSize := by
  unfold maybeReduce
  by_cases hno : noLimit
  · simp [hno]
  · simp only [if_neg hno]
    by_cases hzs : size = 0
    · simp [hzs]
    · simp only [if_neg hzs]
      by_cases hgt : size > s.uncommittedSize
      · simp [hgt]
      · simp [hgt]

/-- **US15** — `size = 0` ⟹ `maybeIncrease` leaves `uncommittedSize` unchanged. -/
theorem US15_maybeIncrease_size_zero_unchanged (s : US) :
    (maybeIncrease s 0).1.uncommittedSize = s.uncommittedSize := by
  have h := US5_maybeIncrease_true_effect s 0 (US3_emptyEntries_increase_true s)
  omega

/-- **US13** — Roundtrip: increase then reduce with same size restores `uncommittedSize`. -/
theorem US13_maybeIncrease_roundtrip (s : US) (size : Nat)
    (hok : (maybeIncrease s size).2 = true) :
    (maybeReduce (maybeIncrease s size).1 false size).1.uncommittedSize = s.uncommittedSize := by
  have heff := US5_maybeIncrease_true_effect s size hok
  simp only [maybeReduce, Bool.false_eq_true, if_false]
  by_cases hzs : size = 0
  · -- size = 0: uncommittedSize unchanged by both operations
    have h15 := US15_maybeIncrease_size_zero_unchanged s
    simp [hzs, h15]
  · simp only [if_neg hzs, heff]
    have hgt : ¬(size > s.uncommittedSize + size) := Nat.not_lt.mpr (Nat.le_add_left size _)
    simp [hgt]

/-- **US14** — `size = 0` ⟹ `maybeReduce` is a no-op. -/
theorem US14_emptyList_reduce_noop (s : US) (noLimit : Bool) :
    maybeReduce s noLimit 0 = (s, true) := by
  unfold maybeReduce
  by_cases hno : noLimit <;> simp [hno]

-- ---------------------------------------------------------------------------
-- US16–US18: Complete characterisations and invariant-preservation
-- ---------------------------------------------------------------------------

/-- **US16** — Complete characterisation of rejection: `maybeIncrease` returns `false`
    **if and only if** all four "allow" conditions fail simultaneously.

    The four allow-guards in `maybeIncrease` are:
    1. `maxUncommittedSize = 0` (no-limit sentinel)
    2. `size = 0` (zero-size entry is always free)
    3. `uncommittedSize = 0` (empty bucket is always free)
    4. `size + uncommittedSize ≤ maxUncommittedSize` (fits in budget)

    Rejection occurs precisely when none of these guards fires. -/
theorem US16_maybeIncrease_false_iff (s : US) (size : Nat) :
    (maybeIncrease s size).2 = false ↔
      s.maxUncommittedSize ≠ 0 ∧ size ≠ 0 ∧ s.uncommittedSize ≠ 0 ∧
      size + s.uncommittedSize > s.maxUncommittedSize := by
  unfold maybeIncrease
  by_cases h1 : s.maxUncommittedSize = 0
  · simp [h1]
  · simp only [if_neg h1]
    by_cases h2 : size = 0
    · simp [h2]
    · simp only [if_neg h2]
      by_cases h3 : s.uncommittedSize = 0
      · simp [h3]
      · simp only [if_neg h3]
        by_cases h4 : size + s.uncommittedSize ≤ s.maxUncommittedSize
        · simp only [if_pos h4]; constructor
          · intro h; exact absurd h (by decide)
          · intro ⟨_, _, _, h5⟩; omega
        · constructor
          · intro _; exact ⟨h1, h2, h3, Nat.lt_of_not_le h4⟩
          · intro _; simp [h4]

/-- **US17** — Complete characterisation of acceptance: `maybeIncrease` returns `true`
    if and only if at least one of the four "free pass" conditions holds.
    This is the dual of US16.  -/
theorem US17_maybeIncrease_true_iff (s : US) (size : Nat) :
    (maybeIncrease s size).2 = true ↔
      s.maxUncommittedSize = 0 ∨ size = 0 ∨ s.uncommittedSize = 0 ∨
      size + s.uncommittedSize ≤ s.maxUncommittedSize := by
  unfold maybeIncrease
  by_cases h1 : s.maxUncommittedSize = 0
  · simp [h1]
  · simp only [if_neg h1]
    by_cases h2 : size = 0
    · simp [h2]
    · simp only [if_neg h2]
      by_cases h3 : s.uncommittedSize = 0
      · simp [h3]
      · simp only [if_neg h3]
        by_cases h4 : size + s.uncommittedSize ≤ s.maxUncommittedSize
        · simp [h4]
        · simp only [if_neg h4]; simp [h1, h2, h3]; omega

/-- **US18** — `maybeReduce` decreases `uncommittedSize` by at most `size`:
    `uncommittedSize_before - size ≤ uncommittedSize_after` (with saturation at 0).

    Both branches of `maybeReduce` satisfy this: the normal branch subtracts exactly
    `size`; the overflow branch sets the result to 0 which is ≥ `before - size`
    (since before < size in that branch).  -/
theorem US18_maybeReduce_ge_sub (s : US) (size : Nat) :
    s.uncommittedSize - size ≤ (maybeReduce s false size).1.uncommittedSize := by
  simp only [maybeReduce, Bool.false_eq_true, ite_false]
  by_cases h1 : size = 0
  · simp only [h1, ite_true]; omega
  · simp only [h1, ite_false]
    by_cases h2 : size > s.uncommittedSize
    · simp only [h2, ite_true]; omega
    · simp only [h2, ite_false]; omega

end FVSquad.UncommittedState
