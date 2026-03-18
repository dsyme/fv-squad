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

/-! ## Safety: at least majority(n) voters have acked ≥ committedIndex -/

/-- **Safety** (core Raft correctness property, non-group-commit path):
    for a non-empty voter set, at least `majority(n)` voters have an acked index
    ≥ `committedIndex`. This means the committed log prefix is genuinely replicated
    to a quorum, satisfying the Raft Log Matching invariant. -/
theorem committedIndex_safety (voters : Finset Nat) (acked : AckedFn)
    (hn : voters.card ≠ 0) :
    countGe voters acked (committedIndex voters acked) ≥ majority voters.card := by
  sorry
  /- Proof sketch:
     Let `sorted = sortedAcked voters acked` and `q = majority voters.card`.
     `committedIndex = sorted[q-1]`.
     Since `sorted` is a descending permutation of `voters.toList.map acked`,
     the first `q` elements of `sorted` all have value ≥ `sorted[q-1]`.
     Each of these corresponds to a distinct voter (since `voters` is a `Finset`).
     Therefore `countGe voters acked sorted[q-1] ≥ q`. -/

/-! ## Maximality: committedIndex is the largest k with the safety property -/

/-- **Maximality** (non-group-commit path):
    for any k strictly greater than committedIndex, fewer than majority(n) voters
    have acked index ≥ k. Together with `committedIndex_safety`, this characterises
    committedIndex as the *maximum* safely-committable index. -/
theorem committedIndex_maximal (voters : Finset Nat) (acked : AckedFn)
    (hn : voters.card ≠ 0) :
    ∀ k : Nat, k > committedIndex voters acked →
    countGe voters acked k < majority voters.card := by
  sorry
  /- Proof sketch:
     Let `sorted = sortedAcked voters acked`, `q = majority voters.card`, `c = sorted[q-1]`.
     For k > c: among the sorted elements, only those at positions 0..pos-1 (where
     `sorted[pos-1] ≥ k > c = sorted[q-1]`) can contribute to `countGe k`.
     Since `sorted` is descending, `pos ≤ q - 1 < q`, so `countGe k < q`. -/

/-! ## Monotonicity: acked indices can only grow → committedIndex can only grow -/

/-- **Monotonicity** (the "Raft never uncommits" invariant):
    if every voter's acked index is pointwise ≥ in round 2 vs round 1, then
    `committedIndex` in round 2 is ≥ round 1. -/
theorem committedIndex_monotone (voters : Finset Nat)
    (acked1 acked2 : AckedFn)
    (hmono : ∀ v ∈ voters, acked1 v ≤ acked2 v)
    (hn : voters.card ≠ 0) :
    committedIndex voters acked1 ≤ committedIndex voters acked2 := by
  sorry
  /- Proof sketch:
     Let `sorted1` and `sorted2` be the sorted acked lists for `acked1` and `acked2`.
     Since `acked1 v ≤ acked2 v` for all v, every element in `sorted1` is ≤ the
     corresponding element in `sorted2` (order statistics are monotone).
     In particular, `sorted1[q-1] ≤ sorted2[q-1]`. -/

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
