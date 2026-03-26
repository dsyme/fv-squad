/-!
# Formal Specification: `limit_size`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises the `limit_size` function from `src/util.rs`.

## What `limit_size` does

```rust
pub fn limit_size<T: PbMessage>(entries: &mut Vec<T>, max: Option<u64>)
```

Truncates `entries` in-place so the total serialised byte-size of retained entries
stays within `max`.  **Always keeps at least the first entry** regardless of size.
No-ops when `max` is `None` or `NO_LIMIT = u64::MAX`.

Rust algorithm (src/util.rs):
1. Return unchanged if `entries.len() ≤ 1`.
2. Return unchanged if `max` is `None` or `u64::MAX`.
3. Scan with `take_while`: always keep the first element (when `size == 0` in the
   accumulator, unconditionally return `true`); keep further elements while the
   running total does not exceed `max`.
4. Truncate to the count produced by that scan.

## Modelling choices

- Type `T` with `compute_size()` is abstracted to type `α` with `size : α → Nat`.
- Rust `Vec` mutation is replaced by a pure function returning the new list.
- `u64` is replaced by unbounded `Nat` (overflow not modelled — precondition).
- `NO_LIMIT` / `None` are unified as `Option.none`.
-/

/-! ## Size helper -/

/-- Sum of the sizes of all elements in a list. -/
def totalSize {α : Type} (size : α → Nat) : List α → Nat
  | []      => 0
  | e :: es => size e + totalSize size es

@[simp] theorem totalSize_nil {α : Type} (size : α → Nat) :
    totalSize size [] = 0 := rfl

@[simp] theorem totalSize_cons {α : Type} (size : α → Nat) (e : α) (es : List α) :
    totalSize size (e :: es) = size e + totalSize size es := rfl

/-- Total size of a prefix is at most total size of the full list. -/
theorem totalSize_take_le {α : Type} (size : α → Nat) (l : List α) (k : Nat) :
    totalSize size (l.take k) ≤ totalSize size l := by
  induction l generalizing k with
  | nil => simp
  | cons e es ih =>
    cases k with
    | zero => simp [totalSize]
    | succ n =>
      simp [List.take_succ_cons, totalSize]
      exact ih n

/-! ## Functional model -/

/-- Count how many entries to keep.
    Mirrors the Rust `take_while` scan with the "always keep the first" rule.
    Parameters: `size` function, `budget`, remaining entries, current count `k`,
    cumulative size so far `cum`. -/
def limitSizeCount {α : Type} (size : α → Nat) (budget : Nat) :
    List α → Nat → Nat → Nat
  | [],      k, _   => k
  | e :: es, k, cum =>
    let cum' := cum + size e
    if k == 0 then
      -- First element: always include (mirrors `if size == 0 { return true }` in Rust)
      limitSizeCount size budget es 1 cum'
    else if cum' > budget then
      k   -- stop here
    else
      limitSizeCount size budget es (k + 1) cum'

/-- The pure functional model of `limit_size`.
    Returns the longest head-prefix of `entries` satisfying the size budget,
    always keeping at least 1 element when the input is non-empty.
    Matches `Option.none` for the unlimited case (covers both `None` and `NO_LIMIT`). -/
def limitSize {α : Type} (size : α → Nat) (entries : List α) (max : Option Nat) :
    List α :=
  match max with
  | none        => entries
  | some budget =>
    if entries.length ≤ 1 then entries
    else entries.take (limitSizeCount size budget entries 0 0)

/-! ## Evaluations (sanity-check against src/util.rs doctest) -/

section Eval

-- Entries are Nat values used as their own size (via `id`).
private def e5 : List Nat := [100, 100, 100, 100, 100]

#eval limitSize id e5 (some 220)   -- [100, 100]  ← 2 entries fit in 220
#eval limitSize id e5 (some 0)     -- [100]        ← budget 0, but keep 1
#eval limitSize id e5 none         -- [100, 100, 100, 100, 100] ← no limit
#eval limitSize id e5 (some 500)   -- [100, 100, 100, 100, 100] ← all fit
#eval limitSize id e5 (some 100)   -- [100]        ← exactly 1 fits (2nd would be 200)
#eval limitSize id e5 (some 99)    -- [100]        ← first kept even over budget
#eval limitSize id ([] : List Nat) (some 100)  -- []
#eval limitSize id [42] (some 0)               -- [42]

end Eval

/-! ## Auxiliary lemmas for `limitSizeCount` -/

/-- `limitSizeCount` result is always ≥ `k` (monotone in the accumulator). -/
theorem limitSizeCount_ge_k {α : Type} (size : α → Nat) (budget : Nat)
    (entries : List α) (k cum : Nat) :
    k ≤ limitSizeCount size budget entries k cum := by
  induction entries generalizing k cum with
  | nil => simp [limitSizeCount]
  | cons e es ih =>
    simp only [limitSizeCount, beq_iff_eq]
    by_cases hk : k = 0
    · subst hk; simp only [if_true]; exact Nat.zero_le _
    · simp only [if_neg hk]
      by_cases hc : cum + size e > budget
      · simp only [if_pos hc]; omega
      · simp only [if_neg hc]; have := ih (k + 1) (cum + size e); omega

/-- `limitSizeCount` result is at most `k + entries.length`. -/
theorem limitSizeCount_le_add_length {α : Type} (size : α → Nat) (budget : Nat)
    (entries : List α) (k cum : Nat) :
    limitSizeCount size budget entries k cum ≤ k + entries.length := by
  induction entries generalizing k cum with
  | nil => simp [limitSizeCount]
  | cons e es ih =>
    simp only [limitSizeCount, beq_iff_eq, List.length_cons]
    by_cases hk : k = 0
    · subst hk; simp only [if_true]; have := ih 1 (cum + size e); omega
    · simp only [if_neg hk]
      by_cases hc : cum + size e > budget
      · simp only [if_pos hc]; omega
      · simp only [if_neg hc]; have := ih (k + 1) (cum + size e); omega

/-- `limitSizeCount` with `k=0, cum=0` unfolds by advancing to `k=1`. -/
@[simp] private theorem limitSizeCount_step_zero {α : Type} (size : α → Nat) (budget : Nat)
    (e : α) (es : List α) :
    limitSizeCount size budget (e :: es) 0 0 = limitSizeCount size budget es 1 (size e) := by
  simp [limitSizeCount]

/-- `limitSizeCount` called with a non-empty list always returns at least 1. -/
theorem limitSizeCount_pos {α : Type} (size : α → Nat) (budget : Nat)
    (e : α) (es : List α) :
    1 ≤ limitSizeCount size budget (e :: es) 0 0 := by
  -- k=0 branch recurses with k=1; the result is ≥ 1 by ge_k.
  rw [limitSizeCount_step_zero]
  exact limitSizeCount_ge_k size budget es 1 (size e)

/-- `limitSizeCount` called with initial `k = 0` never returns more than the list length. -/
theorem limitSizeCount_le_length {α : Type} (size : α → Nat) (budget : Nat)
    (entries : List α) (cum : Nat) :
    limitSizeCount size budget entries 0 cum ≤ entries.length := by
  have h := limitSizeCount_le_add_length size budget entries 0 cum
  simpa using h

/-- When all elements fit in the budget (and `k ≥ 1`), `limitSizeCount` returns `length + k`. -/
private theorem limitSizeCount_all_fit {α : Type} (size : α → Nat) (budget : Nat)
    (entries : List α) (k cum : Nat)
    (hfit : cum + totalSize size entries ≤ budget) (hk : 1 ≤ k) :
    limitSizeCount size budget entries k cum = entries.length + k := by
  induction entries generalizing k cum with
  | nil => simp [limitSizeCount]
  | cons e es ih =>
    simp only [limitSizeCount, beq_iff_eq, List.length_cons, if_neg (show k ≠ 0 by omega)]
    have hce : ¬(cum + size e > budget) := by simp [totalSize] at hfit; omega
    simp only [if_neg hce]
    have := ih (k + 1) (cum + size e) (by simp [totalSize] at hfit; omega) (by omega)
    omega

/-- When all elements fit in the budget, `limitSizeCount` with `k = 0` returns the list length. -/
private theorem limitSizeCount_all_fit_zero {α : Type} (size : α → Nat) (budget : Nat)
    (entries : List α) (hfit : totalSize size entries ≤ budget) :
    limitSizeCount size budget entries 0 0 = entries.length := by
  cases entries with
  | nil => simp [limitSizeCount]
  | cons e es =>
    simp only [limitSizeCount_step_zero, List.length_cons]
    have h := limitSizeCount_all_fit size budget es 1 (size e)
      (by simpa [totalSize] using hfit) (by omega)
    exact h

/-- Size invariant: when called with `k ≥ 1` and `cum ≤ budget`, the cumulative size
    of the kept prefix does not exceed the budget. -/
private theorem limitSizeCount_size_invariant {α : Type} (size : α → Nat) (budget : Nat)
    (entries : List α) (k cum : Nat)
    (hk : 1 ≤ k) (hcum : cum ≤ budget) :
    cum + totalSize size (entries.take (limitSizeCount size budget entries k cum - k)) ≤ budget := by
  induction entries generalizing k cum with
  | nil => simp [limitSizeCount]; exact hcum
  | cons e es ih =>
    simp only [limitSizeCount, beq_iff_eq, if_neg (show k ≠ 0 by omega)]
    by_cases hce : cum + size e > budget
    · simp [if_pos hce, Nat.sub_self]; exact hcum
    · simp only [if_neg hce]
      have hcum' : cum + size e ≤ budget := by omega
      have hr := limitSizeCount_ge_k size budget es (k + 1) (cum + size e)
      have ih' := ih (k + 1) (cum + size e) (by omega) hcum'
      have heq : limitSizeCount size budget es (k + 1) (cum + size e) - k =
                 (limitSizeCount size budget es (k + 1) (cum + size e) - (k + 1)) + 1 := by omega
      rw [heq, @List.take_succ_cons]; simp [totalSize]; omega

/-- Helper: any list with length ≥ 2 can be written as `e :: e' :: rest`. -/
private theorem limitSize_list_ge2 {α : Type} {l : List α} (h : 2 ≤ l.length) :
    ∃ e e' rest, l = e :: e' :: rest := by
  match l with
  | [] => simp at h
  | [_] => simp at h
  | e :: e' :: rest => exact ⟨e, e', rest, rfl⟩

/-- Total size is monotone in the prefix length: taking fewer elements gives a smaller total. -/
private theorem totalSize_take_mono {α : Type} (size : α → Nat) (l : List α)
    (k n : Nat) (hkn : k ≤ n) :
    totalSize size (l.take k) ≤ totalSize size (l.take n) := by
  induction l generalizing k n with
  | nil => simp [totalSize]
  | cons e es ih =>
    cases k with
    | zero => simp [totalSize]
    | succ k' =>
      cases n with
      | zero => omega
      | succ n' =>
        simp only [List.take_succ_cons, totalSize_cons]
        have := ih k' n' (Nat.le_of_succ_le_succ hkn)
        omega

/-- If `limitSizeCount` stops early (count < k + len when k ≥ 1), adding the next element
    would push the cumulative total over the budget. -/
private theorem limitSizeCount_stops_at_budget
    {α : Type} (size : α → Nat) (budget : Nat)
    (entries : List α) (k cum : Nat) (hk : 1 ≤ k)
    (hearly : limitSizeCount size budget entries k cum < k + entries.length) :
    budget < cum + totalSize size
        (entries.take (limitSizeCount size budget entries k cum - k + 1)) := by
  induction entries generalizing k cum with
  | nil =>
    simp only [limitSizeCount, List.length, Nat.add_zero] at hearly; omega
  | cons e' rest ih =>
    have hkne : k ≠ 0 := Nat.ne_of_gt hk
    by_cases hce : cum + size e' > budget
    · -- Function stops here: limitSizeCount = k, so count - k = 0, take 1 = [e']
      have heq : limitSizeCount size budget (e' :: rest) k cum = k := by
        simp only [limitSizeCount, beq_iff_eq, if_neg hkne, if_pos hce]
      rw [heq, Nat.sub_self, Nat.zero_add]
      simp [List.take_succ_cons, totalSize]
      omega
    · -- Function continues recursively
      have hrec : limitSizeCount size budget (e' :: rest) k cum =
                  limitSizeCount size budget rest (k + 1) (cum + size e') := by
        simp only [limitSizeCount, beq_iff_eq, if_neg hkne, if_neg hce]
      rw [hrec] at hearly ⊢
      have hearly' : limitSizeCount size budget rest (k + 1) (cum + size e') <
                     (k + 1) + rest.length := by
        simp only [List.length_cons] at hearly; omega
      have hge := limitSizeCount_ge_k size budget rest (k + 1) (cum + size e')
      have ih' := ih (k + 1) (cum + size e') (by omega) hearly'
      have htake : (e' :: rest).take
                    (limitSizeCount size budget rest (k + 1) (cum + size e') - k + 1) =
                  e' :: rest.take
                    (limitSizeCount size budget rest (k + 1) (cum + size e') - k) := by
        simp [List.take_succ_cons]
      rw [htake, totalSize_cons]
      have heq : limitSizeCount size budget rest (k + 1) (cum + size e') - (k + 1) + 1 =
                 limitSizeCount size budget rest (k + 1) (cum + size e') - k := by omega
      rw [heq] at ih'
      omega

/-- If all elements fit in the budget, `limitSize` is a no-op. -/
private theorem limitSize_all_fit_noop
    {α : Type} (size : α → Nat) (budget : Nat)
    (l : List α) (hfit : totalSize size l ≤ budget) :
    limitSize size l (some budget) = l := by
  simp only [limitSize]
  by_cases h1 : l.length ≤ 1
  · simp [h1]
  · simp only [if_neg h1]
    rw [limitSizeCount_all_fit_zero size budget l hfit]
    simp

/-! ## Specification theorems -/

section Spec

variable {α : Type} (size : α → Nat)

/-! ### P1: Result is a prefix of the input -/

theorem limitSize_is_prefix (entries : List α) (max : Option Nat) :
    limitSize size entries max <+: entries := by
  simp only [limitSize]
  split
  · exact List.prefix_refl entries
  · split
    · exact List.prefix_refl entries
    · exact List.take_prefix _ _

/-! ### P2: Non-empty input is never fully emptied -/

theorem limitSize_nonempty (entries : List α) (max : Option Nat)
    (hne : entries ≠ []) : limitSize size entries max ≠ [] := by
  simp only [limitSize]
  split
  · exact hne
  · split
    · exact hne
    · -- The take returns a non-empty list because limitSizeCount returns ≥ 1
      -- (see limitSizeCount_pos). Full proof in Task 5.
      intro h
      rw [List.take_eq_nil_iff] at h
      rcases h with h1 | h2
      · -- limitSizeCount returned 0, but limitSizeCount_pos says it is ≥ 1
        exact absurd h1 (by
          cases entries with
          | nil => exact absurd rfl hne
          | cons e es => exact Nat.ne_of_gt (limitSizeCount_pos size _ e es))
      · exact hne h2

/-! ### P3: No-op when `max = none` -/

@[simp]
theorem limitSize_none (entries : List α) :
    limitSize size entries none = entries := rfl

/-! ### P4: No-op when input has ≤ 1 elements -/

theorem limitSize_le_one (entries : List α) (hlen : entries.length ≤ 1)
    (max : Option Nat) : limitSize size entries max = entries := by
  simp only [limitSize]
  split
  · rfl
  · simp [hlen]

/-! ### P5: No-op on empty list -/

@[simp]
theorem limitSize_nil (max : Option Nat) :
    limitSize size ([] : List α) max = [] :=
  limitSize_le_one size [] (by simp) max

/-! ### P6: No-op on singleton -/

@[simp]
theorem limitSize_singleton (e : α) (max : Option Nat) :
    limitSize size [e] max = [e] :=
  limitSize_le_one size [e] (by simp) max

/-! ### P7: Result length ≤ original length -/

theorem limitSize_length_le (entries : List α) (max : Option Nat) :
    (limitSize size entries max).length ≤ entries.length :=
  (limitSize_is_prefix size entries max).length_le

/-! ### P8: Result length ≥ 1 when input is non-empty -/

theorem limitSize_length_pos (entries : List α) (hne : entries ≠ [])
    (max : Option Nat) : 0 < (limitSize size entries max).length :=
  List.ne_nil_iff_length_pos.mp (limitSize_nonempty size entries max hne)

/-! ### P9: Size bound
    When the result has > 1 entry, the total size fits within the budget. -/

-- Core case for P9: proved via limitSizeCount_size_invariant.
private theorem limitSize_size_bound_step (e e' : α) (rest : List α) (budget : Nat) :
    (limitSize size (e :: e' :: rest) (some budget)).length = 1 ∨
    totalSize size (limitSize size (e :: e' :: rest) (some budget)) ≤ budget := by
  simp only [limitSize, List.length_cons, show ¬(2 + rest.length ≤ 1) from by omega,
             if_false, limitSizeCount_step_zero]
  by_cases hse : size e > budget
  · left
    have : limitSizeCount size budget (e' :: rest) 1 (size e) = 1 := by
      simp only [limitSizeCount, beq_iff_eq, if_neg (show (1:Nat) ≠ 0 by omega)]
      simp [if_pos (show size e + size e' > budget by omega)]
    rw [this]; simp
  · right
    have hse' : size e ≤ budget := Nat.le_of_not_lt hse
    have hinv := limitSizeCount_size_invariant size budget (e' :: rest) 1 (size e)
                   (by omega) hse'
    have hn := limitSizeCount_ge_k size budget (e' :: rest) 1 (size e)
    rw [show limitSizeCount size budget (e' :: rest) 1 (size e) =
            (limitSizeCount size budget (e' :: rest) 1 (size e) - 1) + 1 from by omega,
        @List.take_succ_cons]
    simp [totalSize]; omega

theorem limitSize_size_bound (entries : List α) (budget : Nat) :
    (limitSize size entries (some budget)).length = 1 ∨
    totalSize size (limitSize size entries (some budget)) ≤ budget := by
  simp only [limitSize]
  by_cases h1 : entries.length ≤ 1
  · simp only [if_pos h1]
    rcases Nat.eq_zero_or_pos entries.length with h0 | hpos
    · right; rw [List.eq_nil_iff_length_eq_zero.mpr h0]; simp [totalSize]
    · left; omega
  · simp only [if_neg h1]
    have h2 : 2 ≤ entries.length := by omega
    obtain ⟨e, e', rest, rfl⟩ := limitSize_list_ge2 h2
    have := limitSize_size_bound_step size e e' rest budget
    simp only [limitSize, List.length_cons,
               show ¬(2 + rest.length ≤ 1) from by omega, if_false] at this
    exact this

/-! ### P10: Maximality
    If the result has k < original-length entries, adding one more would exceed
    the budget. -/

theorem limitSize_maximality (entries : List α) (budget : Nat)
    (hlt : (limitSize size entries (some budget)).length < entries.length) :
    budget < totalSize size
      (entries.take ((limitSize size entries (some budget)).length + 1)) := by
  simp only [limitSize] at *
  by_cases h1 : entries.length ≤ 1
  · simp only [if_pos h1] at hlt; omega
  · simp only [if_neg h1] at *
    have hn_le : limitSizeCount size budget entries 0 0 ≤ entries.length :=
      limitSizeCount_le_length size budget entries 0
    have hlen_n : (entries.take (limitSizeCount size budget entries 0 0)).length =
                  limitSizeCount size budget entries 0 0 := by
      simp [List.length_take, Nat.min_eq_left hn_le]
    rw [hlen_n] at hlt ⊢
    cases entries with
    | nil => simp at h1
    | cons e es =>
      rw [limitSizeCount_step_zero] at hlt ⊢
      simp only [List.length_cons] at hlt
      -- hlt : limitSizeCount ... < es.length + 1; stopping lemma needs < 1 + es.length
      have hlt' : limitSizeCount size budget es 1 (size e) < 1 + es.length := by omega
      have hn_ge1 : 1 ≤ limitSizeCount size budget es 1 (size e) :=
        limitSizeCount_ge_k size budget es 1 (size e)
      have hstop_lem := limitSizeCount_stops_at_budget size budget es 1 (size e) (by omega) hlt'
      have heq1 : limitSizeCount size budget es 1 (size e) - 1 + 1 =
                  limitSizeCount size budget es 1 (size e) := by omega
      rw [heq1] at hstop_lem
      rw [List.take_succ_cons]
      simp [totalSize]
      omega

/-! ### P11: Idempotence — a second application is a no-op. -/

theorem limitSize_idempotent (entries : List α) (max : Option Nat) :
    limitSize size (limitSize size entries max) max =
    limitSize size entries max := by
  cases max with
  | none => simp [limitSize]
  | some budget =>
    simp only [limitSize]
    by_cases h1 : entries.length ≤ 1
    · simp [h1]
    · simp only [if_neg h1]
      -- Let R = entries.take n, n = limitSizeCount ...
      have hn_le : limitSizeCount size budget entries 0 0 ≤ entries.length := by
        have := limitSizeCount_le_add_length size budget entries 0 0; simpa using this
      have hR_len : (entries.take (limitSizeCount size budget entries 0 0)).length =
                    limitSizeCount size budget entries 0 0 := by
        simp [List.length_take, Nat.min_eq_left hn_le]
      by_cases hR1 : (entries.take (limitSizeCount size budget entries 0 0)).length ≤ 1
      · simp only [if_pos hR1]
      · simp only [if_neg hR1]
        -- By P9: totalSize R ≤ budget (since R.length > 1)
        have hp9 : (limitSize size entries (some budget)).length = 1 ∨
                   totalSize size (limitSize size entries (some budget)) ≤ budget :=
          limitSize_size_bound size entries budget
        simp only [limitSize, if_neg h1] at hp9
        rcases hp9 with h | h
        · omega  -- h : length = 1 contradicts hR1
        · -- totalSize R ≤ budget ⟹ applying limitSize again is a no-op
          rw [limitSizeCount_all_fit_zero size budget _ h,
              List.take_take, hR_len, Nat.min_self]

/-! ### P12: Prefix of original is prefix of result (monotone truncation).
    Equivalently: the result is determined by a contiguous head-prefix of the input. -/

theorem limitSize_prefix_of_prefix (entries : List α) (max : Option Nat)
    (k : Nat) (hk : k ≤ (limitSize size entries max).length) :
    limitSize size (entries.take k) max = entries.take k := by
  by_cases hk1 : k ≤ 1
  · apply limitSize_le_one; simp [List.length_take]; omega
  · cases max with
    | none => simp [limitSize]
    | some budget =>
      simp only [limitSize] at hk
      by_cases h1 : entries.length ≤ 1
      · simp only [if_pos h1] at hk; omega
      · simp only [if_neg h1] at hk
        have hn_le : limitSizeCount size budget entries 0 0 ≤ entries.length :=
          limitSizeCount_le_length size budget entries 0
        have hlen_n : (entries.take (limitSizeCount size budget entries 0 0)).length =
                      limitSizeCount size budget entries 0 0 := by
          simp [List.length_take, Nat.min_eq_left hn_le]
        rw [hlen_n] at hk
        -- hk : k ≤ limitSizeCount budget entries 0 0
        -- Get P9 result: count = 1 OR totalSize(entries.take count) ≤ budget
        have hp9 := limitSize_size_bound size entries budget
        simp only [limitSize, if_neg h1] at hp9
        rw [hlen_n] at hp9
        rcases hp9 with hn1 | hfit
        · -- count = 1 but k ≥ 2: contradiction
          omega
        · -- totalSize(entries.take count) ≤ budget; so entries.take k also fits
          have hfit_k : totalSize size (entries.take k) ≤ budget := by
            have hmono := totalSize_take_mono size entries k
                            (limitSizeCount size budget entries 0 0) hk
            omega
          exact limitSize_all_fit_noop size budget (entries.take k) hfit_k

end Spec
