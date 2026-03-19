/-!
# LimitSize — Lean 4 Specification and Implementation Model

Formal specification and implementation model of `limit_size` from `src/util.rs`.
This utility truncates a list of log entries to the longest prefix whose total
serialised byte-size fits within a given budget, subject to a minimum-one guarantee.

## Model scope and approximations

* **Type abstraction**: each log entry is modelled as a single `Nat` representing its
  serialised byte size (`T.compute_size()`). The entry payload is abstracted away.
* **`Option Nat` limit**: the Rust function takes `Option<u64>` where `None` and
  `Some(NO_LIMIT = u64::MAX)` both mean "unlimited". In this model, `None` means
  unlimited. The `u64::MAX` sentinel is not modelled.
* **Pure function**: the Rust function mutates in place; the Lean model is a pure
  function returning the truncated list.
* **`u64` overflow**: the Rust `size` accumulator is `u64`; this model uses unbounded
  `Nat` and does not model overflow.
* **Zero-size entries**: the Rust algorithm accepts all entries whose
  `compute_size() == 0` unconditionally (because the `size == 0` check remains true
  until the first nonzero-sized entry is encountered). This model faithfully captures
  that behaviour.
* **Omitted**: `NO_LIMIT` sentinel, `u64` overflow, in-place mutation, Protobuf
  serialisation cost, error handling.

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Tactic

namespace FVSquad.LimitSize

/-! ## Types -/

/-- `SizeList` models a vector of log entries abstracted to their byte sizes. -/
abbrev SizeList := List Nat

/-! ## Implementation model

The Rust algorithm (paraphrased):

```rust
let mut size: u64 = 0;
count = iter.take_while(|e| {
    if size == 0 { size += e.compute_size(); return true }  // first real entry: always accept
    size += e.compute_size();
    size <= max
}).count();
```

The `size == 0` guard means: accept the entry unconditionally while the running total
is still zero (i.e., while all previous entries had size 0 or this is the first entry).
Once the running total becomes nonzero, subsequent entries are accepted only if the new
cumulative total is ≤ `max`.

Lean model: use `acc` (running total) and `count` (number accepted so far).
Accept an entry iff `acc = 0 ∨ acc + x ≤ lim`.
-/

/-- Core accumulator: scan `rest` starting from running total `acc` and count `count`.
    Returns the total number of entries to keep.

    Accepts entry `x` iff `acc = 0` (running total not yet positive, i.e.\ all prior
    entries had size 0) or `acc + x ≤ lim` (budget not exceeded). -/
def limitSizeGo (lim acc count : Nat) : SizeList → Nat
  | []      => count
  | x :: xs =>
    if acc = 0 ∨ acc + x ≤ lim
    then limitSizeGo lim (acc + x) (count + 1) xs
    else count

/-- `limitSizeCount lim sizes` returns the number of entries to retain. -/
def limitSizeCount (lim : Nat) (sizes : SizeList) : Nat :=
  limitSizeGo lim 0 0 sizes

/-- `limitSize sizes limit` truncates `sizes` to the first `limitSizeCount lim sizes`
    entries.  Returns `sizes` unchanged when `limit = none`. -/
def limitSize (sizes : SizeList) (limit : Option Nat) : SizeList :=
  match limit with
  | none      => sizes
  | some lim  => sizes.take (limitSizeCount lim sizes)

/-! ## Sanity checks via `#eval` and `decide` -/

-- From the doc-comment: entries of 100 bytes, limit 220 → keep first 2
#eval limitSize [100, 100, 100] (some 220)   -- [100, 100]
-- Limit 0: first entry always kept
#eval limitSize [100, 100, 100] (some 0)     -- [100]
-- Unlimited
#eval limitSize [100, 100, 100] none          -- [100, 100, 100]
-- Empty
#eval limitSize [] (some 10)                  -- []
-- Single entry: always kept regardless of limit
#eval limitSize [500] (some 0)                -- [500]
-- Exactly fitting
#eval limitSize [100, 100, 100] (some 300)   -- [100, 100, 100]
-- Zero-size entries: all accepted (acc never becomes positive)
#eval limitSize [0, 0, 0] (some 0)           -- [0, 0, 0]

/-! ## Lemmas about `limitSizeGo` -/

/-- `limitSizeGo` never decreases the count: it is ≥ the initial count. -/
private lemma limitSizeGo_count_ge (lim acc count : Nat) (l : SizeList) :
    count ≤ limitSizeGo lim acc count l := by
  induction l generalizing acc count with
  | nil => simp [limitSizeGo]
  | cons x xs ih =>
    simp only [limitSizeGo]
    split
    · exact Nat.le_trans (Nat.le_succ _) (ih _ _)
    · exact le_refl _

/-- The result of `limitSizeGo` is at most `count + l.length`. -/
private lemma limitSizeGo_le_count_plus_length (lim acc count : Nat) (l : SizeList) :
    limitSizeGo lim acc count l ≤ count + l.length := by
  induction l generalizing acc count with
  | nil => simp [limitSizeGo]
  | cons x xs ih =>
    simp only [limitSizeGo, List.length_cons]
    split
    · calc limitSizeGo lim (acc + x) (count + 1) xs
          ≤ (count + 1) + xs.length := ih _ _
        _ = count + (1 + xs.length) := by omega
    · omega

/-- For a non-empty input, `limitSizeGo` accepts at least one entry (since `acc = 0`
    at the start, the first entry is always accepted). -/
private lemma limitSizeGo_init_pos (lim : Nat) (x : Nat) (xs : SizeList) :
    1 ≤ limitSizeGo lim 0 0 (x :: xs) := by
  -- The condition `0 = 0 ∨ 0 + x ≤ lim` is true (left disjunct), so the first entry
  -- is accepted, giving `limitSizeGo lim x 1 xs`, which is ≥ 1 by count_ge.
  have heq : limitSizeGo lim 0 0 (x :: xs) = limitSizeGo lim x 1 xs := by
    simp [limitSizeGo]
  rw [heq]
  exact limitSizeGo_count_ge lim x 1 xs

/-! ## Lemmas about `limitSizeCount` -/

/-- For a non-empty list, at least one entry is counted. -/
lemma limitSizeCount_pos (lim x : Nat) (xs : SizeList) :
    1 ≤ limitSizeCount lim (x :: xs) := limitSizeGo_init_pos lim x xs

/-- The count is at most the list length. -/
lemma limitSizeCount_le_length (lim : Nat) (sizes : SizeList) :
    limitSizeCount lim sizes ≤ sizes.length := by
  unfold limitSizeCount
  have h := limitSizeGo_le_count_plus_length lim 0 0 sizes
  simpa using h

/-! ## Auxiliary lemmas for budget and maximality proofs -/

/-- **Count shift**: `limitSizeGo` with initial count `c + k` equals the count-zero
    version plus `k`. This lets us relate `limitSizeGo lim acc 1 xs` to
    `limitSizeGo lim acc 0 xs + 1`. -/
private lemma limitSizeGo_count_add (lim acc c k : Nat) (l : SizeList) :
    limitSizeGo lim acc (c + k) l = limitSizeGo lim acc c l + k := by
  induction l generalizing acc c with
  | nil => simp [limitSizeGo]
  | cons x xs ih =>
    simp only [limitSizeGo]
    split_ifs with h
    · have heq : c + k + 1 = (c + 1) + k := by omega
      rw [heq]; exact ih _ _
    · rfl

/-- **Budget lemma** (positive accumulator): when `acc > 0` and `acc ≤ lim`, the sum of
    every entry accepted by `limitSizeGo lim acc 0 l` plus `acc` is at most `lim`.

    Core invariant: once the first nonzero entry sets `acc > 0 ≤ lim`, subsequent entries
    are only accepted if `acc + x ≤ lim`, so the total never exceeds `lim`. -/
private lemma limitSizeGo_budget' (lim acc : Nat) (l : SizeList)
    (hacc_pos : 0 < acc) (hacc_le : acc ≤ lim) :
    (l.take (limitSizeGo lim acc 0 l)).sum + acc ≤ lim := by
  induction l generalizing acc with
  | nil => simp [limitSizeGo, hacc_le]
  | cons x xs ih =>
    unfold limitSizeGo
    by_cases h : acc = 0 ∨ acc + x ≤ lim
    · simp only [h, ↓reduceIte]
      rcases h with heq | hle
      · exact absurd heq (Nat.ne_of_gt hacc_pos)
      · -- Accepted: acc + x ≤ lim
        have hcount : limitSizeGo lim (acc + x) 1 xs = limitSizeGo lim (acc + x) 0 xs + 1 := by
          have := limitSizeGo_count_add lim (acc + x) 0 1 xs; simpa using this
        rw [hcount]
        -- (x :: xs).take (n' + 1) = x :: xs.take n'  (List.take, definitional)
        simp only [List.take_succ_cons, List.sum_cons]
        have := ih (acc + x) (by omega) hle
        omega
    · simp only [h, ↓reduceIte, List.take, List.sum_nil, hacc_le]

/-- **Stop condition**: when `limitSizeGo` terminates early (accepted fewer entries
    than `l.length`), the rejected entry at position `n` would overflow the budget.
    Formally: the running total `(l.take n).sum + acc` is positive, and adding
    `l[n]` would push it above `lim`. -/
private lemma limitSizeGo_stop_condition (lim acc : Nat) (l : SizeList)
    (hlt : limitSizeGo lim acc 0 l < l.length) :
    0 < (l.take (limitSizeGo lim acc 0 l)).sum + acc ∧
    (l.take (limitSizeGo lim acc 0 l)).sum + acc +
      l.get ⟨limitSizeGo lim acc 0 l, hlt⟩ > lim := by
  induction l generalizing acc with
  | nil => simp [limitSizeGo] at hlt
  | cons x xs ih =>
    unfold limitSizeGo at hlt ⊢
    by_cases h : acc = 0 ∨ acc + x ≤ lim
    · -- Accepted branch
      simp only [h, ↓reduceIte] at hlt ⊢
      have hcount : limitSizeGo lim (acc + x) 1 xs = limitSizeGo lim (acc + x) 0 xs + 1 := by
        have := limitSizeGo_count_add lim (acc + x) 0 1 xs; simpa using this
      rw [hcount] at hlt ⊢
      have hlt' : limitSizeGo lim (acc + x) 0 xs < xs.length := by
        simp only [List.length_cons] at hlt; omega
      obtain ⟨hpos, hgt⟩ := ih (acc + x) hlt'
      -- (x :: xs).take (n' + 1) = x :: xs.take n'; get at n'+1 = xs.get at n'
      simp only [List.take_succ_cons, List.sum_cons, List.get_cons_succ]
      omega
    · -- Rejected branch: n = 0; l[0] = x; acc > 0; acc + x > lim
      simp only [h, ↓reduceIte] at hlt ⊢
      push_neg at h
      obtain ⟨hne, hgt⟩ := h
      simp only [List.take, List.sum_nil, List.get_cons_zero]
      omega

/-! ## Main specification theorems -/

/-! ### T1: `limitSize` is a prefix of the input -/

/-- `limitSize sizes limit` is always a prefix of `sizes`. -/
theorem limitSize_is_prefix (sizes : SizeList) (limit : Option Nat) :
    (limitSize sizes limit).IsPrefix sizes := by
  match limit with
  | none => exact List.prefix_refl _
  | some lim =>
    simp only [limitSize]
    exact ⟨sizes.drop (limitSizeCount lim sizes),
           List.take_append_drop (limitSizeCount lim sizes) sizes⟩

/-! ### T2: At least one entry kept when input is non-empty -/

/-- `limitSize` always keeps at least one entry when the input is non-empty. -/
theorem limitSize_length_ge_one (sizes : SizeList) (limit : Option Nat)
    (hne : sizes ≠ []) : 1 ≤ (limitSize sizes limit).length := by
  match limit with
  | none =>
    simp only [limitSize]
    have h := List.length_pos.mpr hne
    omega
  | some lim =>
    match sizes with
    | [] => exact absurd rfl hne
    | x :: xs =>
      simp only [limitSize, List.length_take]
      have h := limitSizeCount_pos lim x xs
      have hlen := limitSizeCount_le_length lim (x :: xs)
      omega

/-! ### T3: Sum ≤ limit when more than one entry is kept (and first entry is nonzero) -/

/-- **Budget safety**: when the result has more than one entry and the first entry has
    positive size (the typical case for Raft log entries), the total byte size of the
    result is within the budget.

    **Proof strategy**: induction on `limitSizeGo` with the invariant that once `acc > 0`,
    we only accept entries that keep `acc ≤ lim`. The first entry is accepted via the
    `acc = 0` branch; once it is accepted (setting `acc = first.size > 0`), subsequent
    entries satisfy `acc + x ≤ lim` at acceptance, so the running total ≤ lim.

    **Corner case**: if `sizes[0] = 0` (zero-size first entry), acc stays 0 longer and
    more entries may be accepted unconditionally. This theorem requires `sizes[0] > 0`. -/
theorem limitSize_sum_le (sizes : SizeList) (lim : Nat)
    (hlen : 2 ≤ (limitSize sizes (some lim)).length)
    (hfirst : ∀ x xs, sizes = x :: xs → 0 < x) :
    (limitSize sizes (some lim)).sum ≤ lim := by
  -- sizes must be non-empty (output ≥ 2 entries ⇒ input non-empty)
  match sizes with
  | [] => simp [limitSize] at hlen
  | x :: xs =>
    simp only [limitSize, limitSizeCount] at hlen ⊢
    have hx_pos : 0 < x := hfirst x xs rfl
    -- Step 1: unfold the first step of limitSizeGo (first entry always accepted: acc = 0)
    have hfirst_step : limitSizeGo lim 0 0 (x :: xs) = limitSizeGo lim x 1 xs := by
      simp [limitSizeGo]
    have hcount_eq : limitSizeGo lim x 1 xs = limitSizeGo lim x 0 xs + 1 := by
      have := limitSizeGo_count_add lim x 0 1 xs; simpa using this
    -- Step 2: output length ≥ 2 implies limitSizeGo lim x 0 xs ≥ 1
    rw [hfirst_step, hcount_eq] at hlen
    have hn' : 1 ≤ limitSizeGo lim x 0 xs := by omega
    -- Step 3: ≥ 1 entries accepted from xs means the first entry of xs was accepted.
    --         Since x > 0, acceptance required x + y ≤ lim, so x ≤ lim.
    have hx_le_lim : x ≤ lim := by
      match xs with
      | [] => simp [limitSizeGo] at hn'
      | y :: ys =>
        -- First entry y was accepted: condition (x = 0 ∨ x + y ≤ lim) must hold
        by_contra hc
        push_neg at hc
        simp [limitSizeGo, show ¬(x = 0 ∨ x + y ≤ lim) from by push_neg; omega] at hn'
    -- Step 4: apply budget lemma with acc = x > 0, x ≤ lim
    have hbudget := limitSizeGo_budget' lim x xs hx_pos hx_le_lim
    -- Output = (x :: xs).take (limitSizeGo lim x 0 xs + 1) = x :: xs.take (limitSizeGo lim x 0 xs)
    rw [hfirst_step, hcount_eq, List.take_succ_cons, List.sum_cons]
    omega

/-! ### T4: Maximality — adding one more entry would exceed the budget -/

/-- **Maximality**: if `limitSize` truncated the input (output strictly shorter), then
    including the next entry would exceed the budget.

    **Proof strategy**: when `limitSizeGo` stops (returns `count` without incrementing),
    the condition `acc = 0 ∨ acc + x ≤ lim` was false, meaning `acc > 0` and `acc + x > lim`.
    Since `acc ≤ lim` at that point (by the budget invariant), the result sum + next entry
    size exceeds `lim`. -/
theorem limitSize_maximal (sizes : SizeList) (lim : Nat)
    (htrunc : (limitSize sizes (some lim)).length < sizes.length) :
    lim < (limitSize sizes (some lim)).sum +
          sizes.get ⟨(limitSize sizes (some lim)).length, htrunc⟩ := by
  simp only [limitSize, limitSizeCount]
  -- n = limitSizeGo lim 0 0 sizes
  set n := limitSizeGo lim 0 0 sizes with hn_def
  -- n < sizes.length (from htrunc, since (sizes.take n).length = min n sizes.length)
  have hlt : n < sizes.length := by
    simp only [List.length_take] at htrunc; omega
  -- Apply stop condition: the entry at position n was rejected
  obtain ⟨_, hgt⟩ := limitSizeGo_stop_condition lim 0 sizes hlt
  -- With acc = 0: (sizes.take n).sum + 0 + sizes.get ⟨n, _⟩ > lim
  simp only [List.sum_nil, zero_add] at hgt
  -- (sizes.take n).length = n  (since n < sizes.length ⇒ min n sizes.length = n)
  have hlen_eq : (sizes.take n).length = n :=
    List.length_take_of_lt hlt
  -- sizes.get ⟨(sizes.take n).length, htrunc⟩ = sizes.get ⟨n, hlt⟩ (same position)
  have hget_eq : sizes.get ⟨(sizes.take n).length, htrunc⟩ = sizes.get ⟨n, hlt⟩ :=
    congrArg sizes.get (Fin.ext hlen_eq)
  rw [hget_eq]
  -- Now goal and hgt both involve (sizes.take n).sum + sizes.get ⟨n, hlt⟩ and lim
  omega

/-! ### T5–T7: Simple structural theorems -/

/-- `limitSize` with `none` is the identity. -/
@[simp]
theorem limitSize_none (sizes : SizeList) : limitSize sizes none = sizes := rfl

/-- `limitSize` of an empty list is empty. -/
@[simp]
theorem limitSize_empty (limit : Option Nat) : limitSize [] limit = [] := by
  cases limit with
  | none     => rfl
  | some lim => simp [limitSize, limitSizeCount, limitSizeGo]

/-- A single-entry list is always returned unchanged. -/
@[simp]
theorem limitSize_singleton (x : Nat) (limit : Option Nat) :
    limitSize [x] limit = [x] := by
  cases limit with
  | none => simp [limitSize]
  | some lim =>
    have hcount : limitSizeCount lim [x] = 1 := by
      simp [limitSizeCount, limitSizeGo]
    simp [limitSize, hcount]

/-! ### T8: Concrete examples verified by `decide` -/

-- From the `limit_size` doc-comment: 5 entries of 100 bytes each, limit 220
example : limitSize [100, 100, 100, 100, 100] (some 220) = [100, 100] := by decide

-- Limit 0: first entry is always kept
example : limitSize [100, 100] (some 0) = [100] := by decide

-- Exact fit: all three entries kept
example : limitSize [100, 100, 100] (some 300) = [100, 100, 100] := by decide

-- First entry exceeds limit: minimum-one guarantee
example : limitSize [500, 100] (some 200) = [500] := by decide

-- All zero-size entries: all kept (acc never becomes positive)
example : limitSize [0, 0, 0] (some 0) = [0, 0, 0] := by decide

-- Mixed: zero-size then nonzero
example : limitSize [0, 100, 100] (some 50) = [0, 100] := by decide

/-! ## Prefix-sum characterisation -/

/-- `prefixSum sizes k` is the sum of the first `k` entries of `sizes`. -/
def prefixSum (sizes : SizeList) (k : Nat) : Nat := (sizes.take k).sum

/-- The result length is within `[1, sizes.length]` for non-empty input with a limit. -/
theorem limitSize_length_bounds (sizes : SizeList) (lim : Nat) (hne : sizes ≠ []) :
    1 ≤ (limitSize sizes (some lim)).length ∧
    (limitSize sizes (some lim)).length ≤ sizes.length := by
  constructor
  · exact limitSize_length_ge_one sizes (some lim) hne
  · simp only [limitSize, List.length_take]
    exact Nat.min_le_right _ _

/-- The result of `limitSize` can be characterised concisely:
    it is the longest prefix of `sizes` such that the prefix has length ≥ 1 AND
    (length = 1 OR prefix sum ≤ `lim`). This matches the informal specification. -/
theorem limitSize_characterisation (sizes : SizeList) (lim : Nat) (hne : sizes ≠ [])
    (hfirst : ∀ x xs, sizes = x :: xs → 0 < x) :
    let result := limitSize sizes (some lim)
    result.IsPrefix sizes ∧
    1 ≤ result.length ∧
    (result.length = 1 ∨ result.sum ≤ lim) := by
  refine ⟨limitSize_is_prefix sizes (some lim),
          limitSize_length_ge_one sizes (some lim) hne, ?_⟩
  by_cases h : 2 ≤ (limitSize sizes (some lim)).length
  · exact Or.inr (limitSize_sum_le sizes lim h hfirst)
  · exact Or.inl (by omega)

end FVSquad.LimitSize
