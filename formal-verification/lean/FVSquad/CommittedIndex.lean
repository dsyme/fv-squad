/-!
# CommittedIndex — Lean 4 Specification and Implementation Model

Formal specification and implementation model of
`MajorityConfig::committed_index` from `src/quorum/majority.rs` (the non-group-commit
path). This is one of the most safety-critical computations in Raft.

## Model scope and approximations

* **Non-group-commit path only**: the `use_group_commit = true` branch is not modelled
  here; it requires extra group-ID bookkeeping and is deferred to a future run.
* **Types**: voter IDs are `Nat` (Rust: `u64`). Acked log indices are also `Nat`.
* **`AckedFn`**: models `impl AckedIndexer` as a pure `Nat → Nat` function, with
  `None` (unknown voters) mapped to `0` via Rust's `unwrap_or_default()`.
* **Empty config return value**: Rust returns `u64::MAX` for empty configs (so that
  `min(empty_result, other)` = `other` in joint quorums). This model returns `0`
  for the empty case to stay in `Nat`; the empty-config contract is stated separately
  as a theorem and the divergence from Rust is explicitly documented there.
* **Stack vs. heap allocation**: the Rust code uses a 7-element stack array for small
  configs and a heap Vec for larger ones; this is a performance detail only. The model
  uses `List` throughout.
* **Omitted**: group-commit extension, concurrency, I/O, `AckedIndexer` trait dispatch,
  Rust's `u64` overflow semantics, memory layout.

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sort
import Mathlib.Tactic
import FVSquad.MajorityQuorum

namespace FVSquad.CommittedIndex

open FVSquad.MajorityQuorum (majority majority_pos majority_gt_half majority_mono)

/-! ## Type abbreviations -/

/-- A function from voter ID to their acknowledged log index.
    Models `impl AckedIndexer` with `None ↦ 0` (via `unwrap_or_default`). -/
abbrev AckedFn := Nat → Nat

/-! ## Algorithmic helper functions

The Rust algorithm:
1. Collect `acked_index(v)` for every `v ∈ voters` (defaulting unknown to `0`).
2. Sort the collected values in **descending** order.
3. Return `sorted[majority(n) - 1]`.
-/

/-- Sort a list of natural numbers in **descending** order. -/
def sortDesc (l : List Nat) : List Nat :=
  l.mergeSort (· ≥ ·)

lemma sortDesc_length (l : List Nat) : (sortDesc l).length = l.length :=
  List.length_mergeSort (· ≥ ·) l

lemma sortDesc_perm (l : List Nat) : (sortDesc l).Perm l :=
  List.perm_mergeSort (· ≥ ·) l

/-- The acked indices for all voters, sorted descending. -/
def sortedAcked (voters : Finset Nat) (acked : AckedFn) : List Nat :=
  sortDesc (voters.toList.map acked)

lemma sortedAcked_length (voters : Finset Nat) (acked : AckedFn) :
    (sortedAcked voters acked).length = voters.card := by
  simp [sortedAcked, sortDesc_length, Finset.length_toList]

/-! ## Declarative characterisation: `countGe`

An alternative (equivalent) characterisation:  `committedIndex = max { k | countGe voters acked k ≥ majority(n) }`.
This is more useful for stating the safety and maximality theorems. -/

/-- Number of voters whose acked index is **at least** `k`. -/
def countGe (voters : Finset Nat) (acked : AckedFn) (k : Nat) : Nat :=
  (voters.filter (fun v => k ≤ acked v)).card

lemma countGe_antitone (voters : Finset Nat) (acked : AckedFn) {j k : Nat} (hjk : j ≤ k) :
    countGe voters acked k ≤ countGe voters acked j := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro v hv
  simp [Finset.mem_filter] at hv ⊢
  exact le_trans hjk hv

/-! ## Implementation model: `committedIndex` -/

/-- `committedIndex` — Lean model of `MajorityConfig::committed_index`
    (non-group-commit path, see module-level approximation notes).

    For non-empty voter sets: sorts all acked indices descending and returns
    the element at position `majority(n) - 1` (0-indexed).

    For the empty voter set: returns `0`. **This diverges from Rust**, which returns
    `u64::MAX` as a sentinel for joint quorums. The empty-config contract is
    captured in `committedIndex_empty_contract` below. -/
def committedIndex (voters : Finset Nat) (acked : AckedFn) : Nat :=
  (sortedAcked voters acked).getD (majority voters.card - 1) 0

/-! ### Sanity checks -/

-- Three voters, acked indices 5, 3, 1. majority(3) = 2. Sorted: [5, 3, 1]. Result = 3.
#eval committedIndex {1, 2, 3}
    (fun v => if v == 1 then 5 else if v == 2 then 3 else 1)
-- Expected: 3 ✓

-- Five voters, acked indices 5, 4, 3, 2, 1. majority(5) = 3. Sorted: [5,4,3,2,1]. Result = 3.
#eval committedIndex {1, 2, 3, 4, 5}
    (fun v => match v with | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | _ => 1)
-- Expected: 3 ✓

-- All same. Any size; majority element equals the common value.
#eval committedIndex {1, 2, 3} (fun _ => 2)
-- Expected: 2 ✓

/-! ## Basic structural lemmas -/

/-- For non-empty voter sets, the quorum position is within the sorted list bounds. -/
lemma quorumPos_lt (voters : Finset Nat) (hn : voters.card ≠ 0) :
    majority voters.card - 1 < (sortedAcked voters (fun _ => 0)).length := by
  rw [sortedAcked_length]
  have h1 := majority_pos voters.card
  omega

lemma quorumPos_lt_acked (voters : Finset Nat) (acked : AckedFn) (hn : voters.card ≠ 0) :
    majority voters.card - 1 < (sortedAcked voters acked).length := by
  rw [sortedAcked_length]
  have h1 := majority_pos voters.card
  omega

/-- For non-empty voter sets, committedIndex equals the element at the quorum position
    in the sorted acked list. -/
theorem committedIndex_eq_nth (voters : Finset Nat) (acked : AckedFn)
    (hn : voters.card ≠ 0) :
    committedIndex voters acked =
    (sortedAcked voters acked).get
      ⟨majority voters.card - 1, quorumPos_lt_acked voters acked hn⟩ := by
  simp [committedIndex]
  rw [List.getD_eq_get _ _ (quorumPos_lt_acked voters acked hn)]

/-! ## Empty config -/

/-- For an empty voter set, committedIndex returns `0` (model simplification).

    **Rust contract**: the Rust implementation returns `u64::MAX` so that a joint
    quorum of form `min(committed_index(empty, l), committed_index(other, l))` equals
    `committed_index(other, l)` — the empty half is effectively ignored.

    **Model note**: in this Lean model we return `0` (staying in `Nat`). Callers of
    joint-quorum logic should be aware that the empty-config case is not modelled
    with the sentinel. -/
theorem committedIndex_empty (acked : AckedFn) :
    committedIndex ∅ acked = 0 := by
  simp [committedIndex, sortedAcked, sortDesc, majority]

/-! ## Proof infrastructure: sorted-list helpers -/

/-- In a `Sorted (· ≥ ·)` list, element at position `i` is ≥ element at position `j`
    whenever `i ≤ j` (earlier positions hold larger or equal values). -/
private lemma sortedDesc_get_mono {l : List Nat} (hl : l.Sorted (· ≥ ·))
    {i j : Fin l.length} (hij : i.val ≤ j.val) : l.get j ≤ l.get i := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · exact le_of_eq (congrArg l.get (Fin.ext h.symm))
  · -- i.val < j.val; use Sorted = Pairwise to compare arbitrary in-order elements
    exact List.pairwise_iff_get.mp hl i j h

/-- `sortedAcked` produces a list sorted in descending order. -/
private lemma sortedAcked_sorted (voters : Finset Nat) (acked : AckedFn) :
    (sortedAcked voters acked).Sorted (· ≥ ·) := by
  simp only [sortedAcked, sortDesc]
  exact List.sorted_mergeSort (· ≥ ·) _

/-- `countGe` is monotone in `acked`: pointwise larger acked values yield a larger (or
    equal) quorum count at every threshold.  This is the key lemma for monotonicity. -/
private lemma countGe_mono_acked (voters : Finset Nat) (acked1 acked2 : AckedFn) (k : Nat)
    (hmono : ∀ v ∈ voters, acked1 v ≤ acked2 v) :
    countGe voters acked1 k ≤ countGe voters acked2 k := by
  unfold countGe
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, Nat.le_trans hv.2 (hmono v hv.1)⟩

/-! ## Safety: at least majority(n) voters have acked ≥ committedIndex -/

/-- **Safety** (core Raft correctness property, non-group-commit path):
    for a non-empty voter set, at least `majority(n)` voters have an acked index
    ≥ `committedIndex`. This means the committed log prefix is genuinely replicated
    to a quorum, satisfying the Raft Log Matching invariant. -/
theorem committedIndex_safety (voters : Finset Nat) (acked : AckedFn)
    (hn : voters.card ≠ 0) :
    countGe voters acked (committedIndex voters acked) ≥ majority voters.card := by
  set n := voters.card
  set q := majority n
  have hq_pos : 1 ≤ q          := majority_pos n
  have hq_le  : q ≤ n          := majority_le n (Nat.pos_of_ne_zero hn)
  set sorted  := sortedAcked voters acked
  have hlen   : sorted.length = n := sortedAcked_length voters acked
  have hpos   : q - 1 < sorted.length := by omega
  -- committedIndex = sorted[q-1]
  have hc_eq  : committedIndex voters acked = sorted.get ⟨q - 1, hpos⟩ :=
    committedIndex_eq_nth voters acked hn
  rw [hc_eq, ge_iff_le]
  set c := sorted.get ⟨q - 1, hpos⟩
  -- sorted is sorted descending
  have hsorted : sorted.Sorted (· ≥ ·) := sortedAcked_sorted voters acked
  -- All elements at positions 0..q-1 of sorted are ≥ c (since sorted is descending
  -- and sorted[q-1] = c).
  have hfirst_q_ge : ∀ (i : Fin sorted.length), i.val < q → c ≤ sorted.get i := by
    intro i hi
    exact sortedDesc_get_mono hsorted (by omega)
  -- The countP / Finset-card connection. We need:
  --   countGe voters acked c ≥ q
  -- which expands to:
  --   (voters.filter (c ≤ acked ·)).card ≥ q
  --
  -- Proof chain:
  -- Step A: sorted.countP (fun x => c ≤ x) ≥ q
  --         (the first q positions of sorted satisfy c ≤ ·, by hfirst_q_ge)
  -- Step B: sorted.countP (fun x => c ≤ x)
  --         = (voters.toList.map acked).countP (fun x => c ≤ x)
  --         (by List.Perm.countP_eq applied to sortDesc_perm)
  -- Step C: (voters.toList.map acked).countP (fun x => c ≤ x)
  --         = voters.toList.countP (fun v => c ≤ acked v)
  --         (by List.countP_map)
  -- Step D: voters.toList.countP (fun v => c ≤ acked v)
  --         = (voters.filter (c ≤ acked ·)).card
  --         (via Finset.card_filter + Multiset.countP_coe / Finset.toList_filter)
  --
  -- Steps B, C, D require exact Mathlib 4.14.0 API names for Multiset/List countP bridge.
  -- Step A is proved below. The full chain is left as sorry pending API verification.

  -- Step A: at least q elements of sorted are ≥ c
  have hstep_A : q ≤ sorted.countP (fun x => decide (c ≤ x)) := by
    -- sorted.take q has length q and all elements ≥ c (by hfirst_q_ge)
    have htake_len : (sorted.take q).length = q :=
      List.length_take_of_le (by omega)
    have hall_ge : ∀ x ∈ sorted.take q, c ≤ x := by
      intro x hx
      rw [List.mem_iff_get] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hi' : i.val < q := by rwa [List.length_take_of_le (by omega)] at hi
      have hi'' : i.val < sorted.length := by omega
      rw [List.get_take _ (by omega)]
      exact hfirst_q_ge ⟨i.val, hi''⟩ hi'
    have hcp_take : (sorted.take q).countP (fun x => decide (c ≤ x)) = q := by
      rw [List.countP_eq_length.mpr (fun x hx => decide_eq_true (hall_ge x hx)),
          htake_len]
    calc q = (sorted.take q).countP (fun x => decide (c ≤ x)) := hcp_take.symm
         _ ≤ sorted.countP (fun x => decide (c ≤ x)) :=
               List.Sublist.countP_le (fun x => decide (c ≤ x)) (List.take_sublist q sorted)

  -- Full chain (Steps B+C+D): sorry pending Mathlib API verification
  -- TODO: fill in using List.Perm.countP_eq, List.countP_map,
  --       and the Finset.card_filter / Multiset.countP_coe bridge.
  sorry

/-! ## Maximality: committedIndex is the largest k with the safety property -/

/-- **Maximality** (non-group-commit path):
    for any k strictly greater than committedIndex, fewer than majority(n) voters
    have acked index ≥ k. Together with `committedIndex_safety`, this characterises
    committedIndex as the *maximum* safely-committable index. -/
theorem committedIndex_maximal (voters : Finset Nat) (acked : AckedFn)
    (hn : voters.card ≠ 0) :
    ∀ k : Nat, k > committedIndex voters acked →
    countGe voters acked k < majority voters.card := by
  intro k hk
  set n := voters.card
  set q := majority n
  have hq_pos : 1 ≤ q          := majority_pos n
  have hq_le  : q ≤ n          := majority_le n (Nat.pos_of_ne_zero hn)
  set sorted  := sortedAcked voters acked
  have hlen   : sorted.length = n := sortedAcked_length voters acked
  have hpos   : q - 1 < sorted.length := by omega
  -- c = sorted[q-1] = committedIndex
  have hc_eq  : committedIndex voters acked = sorted.get ⟨q - 1, hpos⟩ :=
    committedIndex_eq_nth voters acked hn
  set c := sorted.get ⟨q - 1, hpos⟩
  have hck    : c < k := by rwa [← hc_eq]
  -- sorted is sorted descending
  have hsorted : sorted.Sorted (· ≥ ·) := sortedAcked_sorted voters acked
  -- All positions j ≥ q-1 in sorted have sorted[j] ≤ c < k.
  -- Therefore every position where sorted[j] ≥ k must have j < q-1, giving < q such positions.
  -- By the same Finset/countP chain as in safety:
  --   countGe voters acked k = sorted.countP (k ≤ ·) ≤ q - 1 < q.
  -- Step A: positions ≥ q-1 in sorted all have values < k
  have hafter_qth_lt : ∀ (j : Fin sorted.length), q - 1 ≤ j.val → sorted.get j < k := by
    intro j hj
    exact Nat.lt_of_le_of_lt
      (sortedDesc_get_mono hsorted (by omega))
      hck
  -- Step B: sorted.countP (k ≤ ·) ≤ q - 1 < q
  --         (only positions 0..q-2 can have sorted[j] ≥ k, by hafter_qth_lt)
  have hstep_B : sorted.countP (fun x => decide (k ≤ x)) ≤ q - 1 := by
    -- Elements at positions ≥ q-1 in sorted are all < k (by hafter_qth_lt),
    -- so (sorted.drop (q-1)).countP (k ≤ ·) = 0.
    have hnil : (sorted.drop (q - 1)).countP (fun x => decide (k ≤ x)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      rw [List.mem_iff_get] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [List.get_drop]
      have hj : (q - 1 + i.val) < sorted.length :=
        Nat.lt_of_lt_of_le i.isLt (by simp [List.length_drop]; omega)
      have hlt := hafter_qth_lt ⟨q - 1 + i.val, hj⟩ (by omega)
      exact decide_eq_false (Nat.not_le.mpr hlt)
    rw [← List.take_append_drop (q - 1) sorted, List.countP_append] at *
    have hle := List.countP_le_length (fun x => decide (k ≤ x)) (sorted.take (q - 1))
    have htake_len := List.length_take_of_le (n := q - 1) (l := sorted) (by omega)
    omega
  -- Full chain (Steps C+D): countGe voters acked k = sorted.countP (k ≤ ·)
  -- (same bridge as in safety: sorry pending Mathlib API verification)
  -- Combined with hstep_B: countGe voters acked k ≤ q - 1 < q.
  sorry

/-! ## Monotonicity: acked indices can only grow → committedIndex can only grow -/

/-- **Monotonicity** (the "Raft never uncommits" invariant):
    if every voter's acked index is pointwise ≥ in round 2 vs round 1, then
    `committedIndex` in round 2 is ≥ round 1.

    **Proof**: by contradiction — if `committedIndex` decreased, then by `committedIndex_maximal`
    there are fewer than `majority(n)` voters with acked2 ≥ committedIndex1.  But by
    `committedIndex_safety` there are ≥ majority(n) voters with acked1 ≥ committedIndex1,
    and since acked2 ≥ acked1 pointwise, this contradicts the maximality bound. -/
theorem committedIndex_monotone (voters : Finset Nat)
    (acked1 acked2 : AckedFn)
    (hmono : ∀ v ∈ voters, acked1 v ≤ acked2 v)
    (hn : voters.card ≠ 0) :
    committedIndex voters acked1 ≤ committedIndex voters acked2 := by
  by_contra hlt
  push_neg at hlt
  -- Suppose committedIndex voters acked2 < committedIndex voters acked1.
  -- By maximality on acked2: countGe voters acked2 (committedIndex voters acked1) < q.
  have h_max := committedIndex_maximal voters acked2 hn
      (committedIndex voters acked1) hlt
  -- By safety on acked1: countGe voters acked1 (committedIndex voters acked1) ≥ q.
  have h_safe := committedIndex_safety voters acked1 hn
  -- Since acked1 ≤ acked2 pointwise, countGe is monotone in acked:
  -- countGe voters acked1 (committedIndex voters acked1)
  --   ≤ countGe voters acked2 (committedIndex voters acked1).
  have h_mono_count := countGe_mono_acked voters acked1 acked2
      (committedIndex voters acked1) hmono
  -- Now: q ≤ countGe acked1 (…) ≤ countGe acked2 (…) < q — contradiction.
  omega

/-! ## Singleton voter set -/

/-- For a single voter, committedIndex equals that voter's acked index.
    (`majority 1 = 1`, so we pick the 0th element of the 1-element sorted list.) -/
theorem committedIndex_singleton (v : Nat) (acked : AckedFn) :
    committedIndex {v} acked = acked v := by
  simp [committedIndex, sortedAcked, sortDesc, majority, Finset.toList_singleton]

/-! ## Lower bound -/

/-- committedIndex is ≥ 0 (trivially true for `Nat`, stated for documentation). -/
theorem committedIndex_nonneg (voters : Finset Nat) (acked : AckedFn) :
    0 ≤ committedIndex voters acked :=
  Nat.zero_le _

/-! ## Relation to countGe -/

/-- `countGe voters acked 0 = voters.card`: every voter has acked index ≥ 0. -/
theorem countGe_zero (voters : Finset Nat) (acked : AckedFn) :
    countGe voters acked 0 = voters.card := by
  simp [countGe]

/-! ## Note on the group-commit extension -/
/--
  **Group-commit path** (`use_group_commit = true`) — NOT modelled here.

  When `use_group_commit = true`, the algorithm adds a secondary criterion ensuring
  that the committed index is acknowledged by voters from at least two distinct groups
  (non-zero `group_id`). The key cases are:

  1. **Cross-group quorum found**: return `min(first_cross_group_index, quorum_index)` with
     `group_commit_used = true`.
  2. **All voters in same group**: return `(quorum_index, false)` — group commit did not apply.
  3. **Some voters have group_id = 0**: return `(min_of_all_acked, false)` — conservative fallback.

  The group-commit path is intended for cross-datacenter safety and is significantly
  more complex to formalise. It is deferred to a future Lean Squad run.
-/

end FVSquad.CommittedIndex
