import FVSquad.CommittedIndex
import FVSquad.QuorumRecentlyActive

/-!
# Safety Composition: CommittedIndex × HasQuorum × QuorumRecentlyActive

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Cross-module theorems connecting three quorum-related models:

- **CommittedIndex** (`src/quorum/majority.rs`): computes the largest log index
  acknowledged by a majority of voters.
- **HasQuorum** (`src/tracker.rs`): tests whether a set of nodes forms a majority.
- **QuorumRecentlyActive** (`src/tracker.rs`): tests whether recently-active nodes
  form a majority.

## Core result

The principal theorem (`SC4_raft_log_safety`) is a **Raft log-safety certificate**:
for any two acked-index functions over the same non-empty voter configuration, the two
committed indices share a common *witness voter* — a node that individually acknowledged
both committed indices.

This formalises the core Raft safety invariant: because any two majorities over the same
voter list must intersect (proved as `quorum_intersection`), no two different log
prefixes can be simultaneously committed.

Additional theorems show that `committedIndex` and `hasQuorum` with a threshold predicate
are equivalent (SC6), and that the recently-active quorum and the commit quorum must share
at least one voter (SC8–SC9), ensuring leader election safety.

## Theorem table

| ID  | Name                                    | Description                                                        |
|-----|-----------------------------------------|--------------------------------------------------------------------|
| SC1 | `SC1_overlapCount_eq_countGe`           | Bridge: `overlapCount` = `countGe` for threshold predicate         |
| SC2 | `SC2_committedIndex_threshold_hasQuorum`| threshold ≤ committedIndex → threshold set is a quorum             |
| SC3 | `SC3_committedIndex_implies_hasQuorum`  | Committed index yields a quorum certificate (SC2 at k=committedIndex)|
| SC4 | `SC4_raft_log_safety`                   | **Main**: two committed indices share a witness voter              |
| SC5 | `SC5_hasQuorum_implies_committedIndex_ge`| Converse: quorum at threshold k → committedIndex ≥ k             |
| SC6 | `SC6_committedIndex_quorum_iff`         | Biconditional: committedIndex ≥ k ↔ threshold quorum              |
| SC7 | `SC7_committedIndex_witness`            | A concrete voter acknowledged the committed index                  |
| SC8 | `SC8_quorumActive_committed_witness`    | ∃ voter that is both recently-active AND committed                 |
| SC9 | `SC9_quorumActive_and_commit_share_voter`| Recently-active quorum ∩ commit quorum ≠ ∅                       |

## Modelling notes

- All models are purely functional; I/O, message passing, and concurrency are omitted.
- Voter IDs are `Nat` (Rust: `u64`); acked indices are `Nat` (Rust: `u64`).
- `AckedFn := Nat → Nat` models the `AckedIndexer` trait from `src/quorum/majority.rs`.
- Voter lists are `List Nat`; duplicates assumed absent where it matters.
-/

open FVSquad.CommittedIndex
open FVSquad.QuorumRecentlyActive
open FVSquad.Progress

namespace FVSquad.SafetyComposition

/-! ## Helper lemma -/

/-- `overlapCount` equals the length of the filter list. -/
private theorem overlapCount_eq_filter_length (voters : List Nat) (s : Nat → Bool) :
    overlapCount voters s = (voters.filter s).length := by
  induction voters with
  | nil => simp [overlapCount]
  | cons v vs ih =>
    rw [overlapCount_cons, List.filter_cons]
    cases h : s v <;> simp [ih] <;> omega

/-! ## SC1: Bridge between `overlapCount` and `countGe` -/

/-- **SC1**: `overlapCount voters (fun v => decide (acked v ≥ k))` equals
    `countGe voters acked k`.

    Both count the number of voters whose acknowledged index is at least `k`, but
    `overlapCount` is the idiom used by `HasQuorum` (a general set-membership counter),
    while `countGe` is the specialised version used by `CommittedIndex`.

    This bridge lemma is the linchpin of all subsequent cross-module theorems. -/
theorem SC1_overlapCount_eq_countGe (voters : List Nat) (acked : AckedFn) (k : Nat) :
    overlapCount voters (fun v => decide (acked v ≥ k)) = countGe voters acked k := by
  rw [overlapCount_eq_filter_length]
  simp [countGe]

/-! ## SC2–SC3: Committed index implies quorum certificate -/

/-- **SC2**: If voters is non-empty and `k ≤ committedIndex voters acked`, then
    the set `{ v | acked v ≥ k }` forms a quorum over `voters`.

    Proof chain:
    - `committedIndex_safety`: majority ≤ countGe(committedIndex)
    - `countGe_antitone`: countGe(committedIndex) ≤ countGe(k)  (since k ≤ committedIndex)
    - `SC1`: countGe(k) = overlapCount(k)
    - `hasQuorum_iff_overlap`: quorum holds iff overlapCount ≥ majority -/
theorem SC2_committedIndex_threshold_hasQuorum
    (hd : Nat) (tl : List Nat) (acked : AckedFn) (k : Nat)
    (hk : k ≤ committedIndex (hd :: tl) acked) :
    hasQuorum (hd :: tl) (fun v => decide (acked v ≥ k)) = true := by
  have hn    : 0 < (hd :: tl).length := by simp
  have hsafe := committedIndex_safety (hd :: tl) acked hn
  have hanti := countGe_antitone (hd :: tl) acked k (committedIndex (hd :: tl) acked) hk
  have heq   := SC1_overlapCount_eq_countGe (hd :: tl) acked k
  rw [hasQuorum_iff_overlap]
  right
  calc majority (hd :: tl).length
      ≤ countGe (hd :: tl) acked (committedIndex (hd :: tl) acked) := hsafe
    _ ≤ countGe (hd :: tl) acked k                                  := hanti
    _ = overlapCount (hd :: tl) (fun v => decide (acked v ≥ k))     := heq.symm

/-- **SC3**: The committed index itself forms a quorum certificate.
    Specialises SC2 to `k = committedIndex voters acked`. -/
theorem SC3_committedIndex_implies_hasQuorum
    (hd : Nat) (tl : List Nat) (acked : AckedFn) :
    hasQuorum (hd :: tl) (fun v => decide (acked v ≥ committedIndex (hd :: tl) acked)) = true :=
  SC2_committedIndex_threshold_hasQuorum hd tl acked _ (Nat.le_refl _)

/-! ## SC4: Raft log safety (the main theorem) -/

/-- **SC4** — **Raft log safety**: for any two acknowledgment functions `acked1` and
    `acked2` over the same non-empty voter configuration, there exists a voter `w` that
    individually witnessed *both* committed indices.

    Formally:
    ```
    ∃ w ∈ (hd :: tl),
      acked1 w ≥ committedIndex (hd :: tl) acked1 ∧
      acked2 w ≥ committedIndex (hd :: tl) acked2
    ```

    **Interpretation**: Raft commits an entry when a majority of voters acknowledge it.
    By `quorum_intersection`, any two majorities over the same voter list share at least
    one node.  That shared node `w` is the *honest broker*: it participated in both commit
    rounds, preventing two conflicting log prefixes from ever being simultaneously committed.

    This is the formal counterpart of the standard Raft safety argument
    (Ongaro & Ousterhout, §5.4). -/
theorem SC4_raft_log_safety
    (hd : Nat) (tl : List Nat) (acked1 acked2 : AckedFn) :
    ∃ w ∈ (hd :: tl),
      acked1 w ≥ committedIndex (hd :: tl) acked1 ∧
      acked2 w ≥ committedIndex (hd :: tl) acked2 := by
  have hq1 := SC3_committedIndex_implies_hasQuorum hd tl acked1
  have hq2 := SC3_committedIndex_implies_hasQuorum hd tl acked2
  obtain ⟨w, hmem, h1, h2⟩ :=
    quorum_intersection_mem hd tl
      (fun v => decide (acked1 v ≥ committedIndex (hd :: tl) acked1))
      (fun v => decide (acked2 v ≥ committedIndex (hd :: tl) acked2))
      hq1 hq2
  exact ⟨w, hmem,
    by simpa [decide_eq_true_eq] using h1,
    by simpa [decide_eq_true_eq] using h2⟩

/-! ## SC5: Converse direction -/

/-- **SC5**: If `hasQuorum voters (fun v => decide (acked v ≥ k)) = true` and voters
    is non-empty, then `committedIndex voters acked ≥ k`.

    **Proof** (by contradiction): if `committedIndex < k`, then `committedIndex_maximality`
    gives `countGe(k) < majority`, contradicting the quorum hypothesis. -/
theorem SC5_hasQuorum_implies_committedIndex_ge
    (hd : Nat) (tl : List Nat) (acked : AckedFn) (k : Nat)
    (hq : hasQuorum (hd :: tl) (fun v => decide (acked v ≥ k)) = true) :
    k ≤ committedIndex (hd :: tl) acked := by
  have heq  := SC1_overlapCount_eq_countGe (hd :: tl) acked k
  rw [hasQuorum_iff_overlap] at hq
  cases hq with
  | inl h => exact absurd h (List.cons_ne_nil _ _)
  | inr hov =>
    rw [heq] at hov
    -- hov : majority (hd :: tl).length ≤ countGe (hd :: tl) acked k
    -- By committedIndex_maximality, if committedIndex < k then countGe < majority.
    -- Combined with hov, this is a contradiction, so k ≤ committedIndex.
    rcases Nat.lt_or_ge (committedIndex (hd :: tl) acked) k with hlt | hge
    · have hmax := committedIndex_maximality (hd :: tl) acked k hlt
      omega
    · exact hge

/-! ## SC6: Biconditional -/

/-- **SC6** — **Biconditional**: For non-empty voters,
    ```
    hasQuorum voters (fun v => decide (acked v ≥ k)) = true
      ↔  k ≤ committedIndex voters acked
    ```
    Combines SC2 (←) and SC5 (→) into a clean characterisation:
    `committedIndex` is the *largest* `k` for which the threshold set forms a quorum. -/
theorem SC6_committedIndex_quorum_iff
    (hd : Nat) (tl : List Nat) (acked : AckedFn) (k : Nat) :
    hasQuorum (hd :: tl) (fun v => decide (acked v ≥ k)) = true ↔
    k ≤ committedIndex (hd :: tl) acked := by
  constructor
  · exact SC5_hasQuorum_implies_committedIndex_ge hd tl acked k
  · exact SC2_committedIndex_threshold_hasQuorum hd tl acked k

/-! ## SC7: Concrete witness -/

/-- **SC7**: For any non-empty voter list, there exists a concrete voter `w` in the
    list that individually acknowledged the committed index.

    This shows `committedIndex` is not merely an upper bound — at least one voter
    actually acknowledged it. -/
theorem SC7_committedIndex_witness
    (hd : Nat) (tl : List Nat) (acked : AckedFn) :
    ∃ w ∈ (hd :: tl), acked w ≥ committedIndex (hd :: tl) acked := by
  have hq  := SC3_committedIndex_implies_hasQuorum hd tl acked
  rw [hasQuorum_iff_overlap] at hq
  cases hq with
  | inl h => exact absurd h (List.cons_ne_nil _ _)
  | inr hov =>
    have hmaj : 1 ≤ majority (hd :: tl).length := by unfold majority; omega
    obtain ⟨w, hmem, hw⟩ :=
      overlapCount_pos_mem (hd :: tl)
        (fun v => decide (acked v ≥ committedIndex (hd :: tl) acked))
        (by omega)
    exact ⟨w, hmem, by simpa [decide_eq_true_eq] using hw⟩

/-! ## SC8–SC9: Composition with QuorumRecentlyActive -/

/-- **SC8**: If `quorumRecentlyActive voters entries perspectiveOf = true` and
    `hasQuorum voters (fun v => decide (acked v ≥ k)) = true`, and voters is non-empty,
    then there exists a voter `w` that is **both** recently active **and** has acknowledged
    index ≥ `k`.

    **Interpretation**: the leader's liveness quorum (recently-active nodes) and the
    commit quorum (nodes that acknowledged ≥ k) must share at least one voter. -/
theorem SC8_quorumActive_committed_witness
    (hd : Nat) (tl : List Nat) (acked : AckedFn)
    (entries : List (Nat × Progress)) (perspectiveOf : Nat) (k : Nat)
    (hqra : quorumRecentlyActive (hd :: tl) entries perspectiveOf = true)
    (hqk  : hasQuorum (hd :: tl) (fun v => decide (acked v ≥ k)) = true) :
    ∃ w ∈ (hd :: tl), isActive entries perspectiveOf w = true ∧ acked w ≥ k := by
  rw [quorumRecentlyActive_def] at hqra
  obtain ⟨w, hmem, ha, hk⟩ :=
    quorum_intersection_mem hd tl
      (isActive entries perspectiveOf)
      (fun v => decide (acked v ≥ k))
      hqra hqk
  exact ⟨w, hmem, ha, by simpa [decide_eq_true_eq] using hk⟩

/-- **SC9** — **Leader election safety**: if `quorumRecentlyActive voters entries
    perspectiveOf = true` and voters is non-empty, then there exists a voter `w` that is
    recently active **and** has acknowledged the committed index.

    **Interpretation**: any newly elected leader (whose support forms a recently-active
    quorum) necessarily includes a voter `w` that witnessed the committed index.  In Raft,
    this prevents a new leader from committing divergent entries without first replicating
    all previously committed entries.

    Combines SC3 (commit quorum) with SC8 (active ∩ commit quorum intersection). -/
theorem SC9_quorumActive_and_commit_share_voter
    (hd : Nat) (tl : List Nat) (acked : AckedFn)
    (entries : List (Nat × Progress)) (perspectiveOf : Nat)
    (hqra : quorumRecentlyActive (hd :: tl) entries perspectiveOf = true) :
    ∃ w ∈ (hd :: tl),
      isActive entries perspectiveOf w = true ∧
      acked w ≥ committedIndex (hd :: tl) acked := by
  exact SC8_quorumActive_committed_witness hd tl acked entries perspectiveOf
    (committedIndex (hd :: tl) acked)
    hqra
    (SC3_committedIndex_implies_hasQuorum hd tl acked)

/-! ## Evaluations -/

section Eval

-- SC6 illustration: majority(3) = 2; threshold k=4; acked = (1↦5, 2↦4, 3↦3)
-- overlapCount [1,2,3] (v ≥ 4) = 2 ≥ majority(3) = 2 → quorum = true. SC6 → committedIndex ≥ 4.
#eval (hasQuorum [1, 2, 3] (fun v => decide ((if v == 1 then 5 else if v == 2 then 4 else 3) ≥ 4)))
-- expected: true (voters 1, 2 each ≥ 4, count = 2 ≥ majority(3)=2)

-- Threshold k=5: only voter 1 satisfies (acked 1 = 5 ≥ 5). Count = 1 < 2. Not a quorum.
#eval (hasQuorum [1, 2, 3] (fun v => decide ((if v == 1 then 5 else if v == 2 then 4 else 3) ≥ 5)))
-- expected: false

-- committedIndex [1,2,3] with acked = (1↦5, 2↦4, 3↦3): sorted desc = [5,4,3]; majority(3)=2; result=sorted[1]=4
#eval FVSquad.CommittedIndex.committedIndex [1, 2, 3]
      (fun v => if v == 1 then 5 else if v == 2 then 4 else 3)
-- expected: 4

end Eval

end FVSquad.SafetyComposition
