/-!
# TallyVotes and HasQuorum — Lean 4 Specification

Formal specification of `ProgressTracker::tally_votes` and `ProgressTracker::has_quorum`
from `raft-rs` (`src/tracker.rs`).

## Model scope and approximations

* **Types**: Voter IDs are `Nat` (Rust: `u64`; overflow irrelevant for these algebraic
  properties).
* **`voters`**: modelled as a `Finset Nat` (no duplicate IDs; hash-map details irrelevant).
* **`votes`**: modelled as a total function `Nat → Option Bool` (Rust: `HashMap<u64, bool>`;
  keys absent from the map are `None`).
* **Joint quorum (two-phase config)**: *not* modelled here — we model the single-phase
  majority case (`outgoing = ∅`). Joint-quorum safety is verified in `JointQuorum.lean`.
* **Omitted**: concurrency, I/O, error handling, memory layout, `AckedIndexer` trait.

The `grantedCount`/`rejectedCount` definitions reuse the `yesCount`/`voteResult`
infrastructure from `MajorityQuorum.lean`.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import FVSquad.MajorityQuorum

namespace FVSquad.TallyVotes

open FVSquad.MajorityQuorum

/-! ## Type aliases -/

/-- A vote assignment: total function from node ID to optional vote.
    `None` means the node has not yet voted. -/
abbrev VoteMap := Nat → Option Bool

/-! ## Core model: vote counting -/

/-- Number of voter-members that have voted "yes". -/
def grantedCount (voters : Finset Nat) (votes : VoteMap) : Nat :=
  (voters.filter (fun v => votes v = some true)).card

/-- Number of voter-members that have voted "no". -/
def rejectedCount (voters : Finset Nat) (votes : VoteMap) : Nat :=
  (voters.filter (fun v => votes v = some false)).card

/-- Number of voter-members that have not yet voted. -/
def pendingCount (voters : Finset Nat) (votes : VoteMap) : Nat :=
  (voters.filter (fun v => votes v = none)).card

/-- `tallyVotes` returns `(granted, rejected, result)`, modelling `tally_votes`. -/
def tallyVotes (voters : Finset Nat) (votes : VoteMap) : Nat × Nat × VoteResult :=
  (grantedCount voters votes, rejectedCount voters votes, voteResult voters votes)

/-! ## Connecting `grantedCount` to `MajorityQuorum.yesCount` -/

/-- `grantedCount` equals `yesCount` from MajorityQuorum — definitionally equal. -/
theorem grantedCount_eq_yesCount (voters : Finset Nat) (votes : VoteMap) :
    grantedCount voters votes = yesCount voters votes := rfl

/-- `pendingCount` equals `missingCount` from MajorityQuorum — definitionally equal. -/
theorem pendingCount_eq_missingCount (voters : Finset Nat) (votes : VoteMap) :
    pendingCount voters votes = missingCount voters votes := rfl

/-! ## PROP-1: Key bound: granted + rejected ≤ |voters| -/

/-- The granted and rejected sets are disjoint subsets of `voters`. -/
private theorem granted_rejected_disjoint (voters : Finset Nat) (votes : VoteMap) :
    Disjoint
      (voters.filter (fun v => votes v = some true))
      (voters.filter (fun v => votes v = some false)) := by
  simp only [Finset.disjoint_filter]
  intro x _ hyes hno
  simp [hyes] at hno

/-- PROP-1: `granted + rejected ≤ |voters|`: total observed votes cannot exceed the
    voter population. This is the primary safety property of `tally_votes`. -/
theorem tally_bound (voters : Finset Nat) (votes : VoteMap) :
    grantedCount voters votes + rejectedCount voters votes ≤ voters.card := by
  have hdisj := granted_rejected_disjoint voters votes
  rw [grantedCount, rejectedCount, ← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_union, Finset.mem_filter] at hx
  exact hx.elim And.left And.left

/-! ## PROP-2: Partition of voter set -/

/-- PROP-2: The three disjoint sets (granted, rejected, pending) partition `voters` exactly. -/
theorem tally_partition (voters : Finset Nat) (votes : VoteMap) :
    grantedCount voters votes + rejectedCount voters votes + pendingCount voters votes =
    voters.card := by
  simp only [grantedCount, rejectedCount, pendingCount]
  have hdisj12 := granted_rejected_disjoint voters votes
  have hdisj13 : Disjoint
      (voters.filter (fun v => votes v = some true))
      (voters.filter (fun v => votes v = none)) := by
    simp only [Finset.disjoint_filter]
    intro x _ hyes hnone; simp [hyes] at hnone
  have hdisj23 : Disjoint
      (voters.filter (fun v => votes v = some false))
      (voters.filter (fun v => votes v = none)) := by
    simp only [Finset.disjoint_filter]
    intro x _ hno hnone; simp [hno] at hnone
  have hdisj123 : Disjoint
      (voters.filter (fun v => votes v = some true) ∪
       voters.filter (fun v => votes v = some false))
      (voters.filter (fun v => votes v = none)) :=
    Finset.disjoint_union_left.mpr ⟨hdisj13, hdisj23⟩
  have hunion : voters = voters.filter (fun v => votes v = some true) ∪
                         voters.filter (fun v => votes v = some false) ∪
                         voters.filter (fun v => votes v = none) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hv
      rcases votes v with (_ | b)
      · exact Or.inr ⟨hv, rfl⟩
      · cases b
        · exact Or.inl (Or.inr ⟨hv, rfl⟩)
        · exact Or.inl (Or.inl ⟨hv, rfl⟩)
    · intro h
      rcases h with ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
  conv_rhs => rw [hunion]
  rw [Finset.card_union_of_disjoint hdisj123, Finset.card_union_of_disjoint hdisj12]

/-! ## PROP-3: Consistency of tallyVotes VoteResult -/

/-- PROP-3: The VoteResult in `tallyVotes` is exactly `voteResult voters votes`. -/
theorem tallyVotes_result (voters : Finset Nat) (votes : VoteMap) :
    (tallyVotes voters votes).2.2 = voteResult voters votes := rfl

/-- On an empty voter set, tallyVotes returns (0, 0, Won). -/
theorem tallyVotes_empty (votes : VoteMap) :
    tallyVotes ∅ votes = (0, 0, VoteResult.Won) := by
  simp [tallyVotes, grantedCount, rejectedCount, voteResult]

/-- If no voters have voted, result is Pending for non-empty voter set. -/
theorem tallyVotes_no_votes (voters : Finset Nat) (hne : voters.card ≠ 0) :
    tallyVotes voters (fun _ => none) = (0, 0, VoteResult.Pending) := by
  simp [tallyVotes, grantedCount, rejectedCount, voteResult, yesCount, missingCount,
        majority, hne]
  omega

/-- Non-voter votes are ignored: changing a non-voter's vote doesn't affect counts. -/
theorem grantedCount_nonvoter (voters : Finset Nat) (votes : VoteMap) (v : Nat)
    (hv : v ∉ voters) (b : Bool) :
    grantedCount voters (fun w => if w = v then some b else votes w) =
    grantedCount voters votes := by
  simp only [grantedCount]
  congr 1
  apply Finset.filter_congr
  intro w hw
  simp [ne_of_mem_of_not_mem hw hv]

/-- Non-voter votes are ignored for `rejectedCount` too. -/
theorem rejectedCount_nonvoter (voters : Finset Nat) (votes : VoteMap) (v : Nat)
    (hv : v ∉ voters) (b : Bool) :
    rejectedCount voters (fun w => if w = v then some b else votes w) =
    rejectedCount voters votes := by
  simp only [rejectedCount]
  congr 1
  apply Finset.filter_congr
  intro w hw
  simp [ne_of_mem_of_not_mem hw hv]

/-! ## HasQuorum model -/

/-- A synthetic vote assignment for `has_quorum`: members of `potQuorum` vote yes,
    others don't vote. This mirrors the `|id| potential_quorum.get(&id).map(|_| true)`
    closure in the Rust code. -/
def quorumVotes (potQuorum : Finset Nat) (v : Nat) : Option Bool :=
  if v ∈ potQuorum then some true else none

/-- `hasQuorum voters potQuorum` — pure functional model of `has_quorum`.
    Returns `true` iff `potQuorum` contains enough voters to form a majority. -/
def hasQuorum (voters : Finset Nat) (potQuorum : Finset Nat) : Bool :=
  voteResult voters (quorumVotes potQuorum) == VoteResult.Won

/-! ## Helper: yesCount for membership check -/

/-- The `yesCount` for membership-based votes equals the intersection cardinality. -/
private lemma yesCount_quorumVotes (voters potQuorum : Finset Nat) :
    yesCount voters (quorumVotes potQuorum) =
    (voters.filter (fun v => v ∈ potQuorum)).card := by
  simp only [yesCount, quorumVotes]
  congr 1
  ext v
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hv, heq⟩
    split_ifs at heq with h
    · exact ⟨hv, h⟩
    · simp at heq
  · intro ⟨hv, hmem⟩
    exact ⟨hv, by simp [hmem]⟩

/-- The `yesCount` for membership-based votes also equals `(voters ∩ potQuorum).card`. -/
lemma yesCount_quorumVotes_inter (voters potQuorum : Finset Nat) :
    yesCount voters (quorumVotes potQuorum) = (voters ∩ potQuorum).card := by
  rw [yesCount_quorumVotes]
  congr 1
  ext v
  simp [Finset.mem_inter, Finset.mem_filter]

/-! ## PROP-4: Empty voter config always has quorum -/

/-- PROP-4: Empty voter config: `hasQuorum` always returns `true`
    (empty config wins by convention). -/
theorem hasQuorum_empty_config (potQuorum : Finset Nat) :
    hasQuorum ∅ potQuorum = true := by
  simp [hasQuorum, voteResult]

/-! ## PROP-5: Empty potential quorum never has quorum (for non-empty voters) -/

/-- PROP-5: Empty potential quorum: never has quorum unless voter set is also empty. -/
theorem hasQuorum_empty_set (voters : Finset Nat) (hne : voters.card ≠ 0) :
    hasQuorum voters ∅ = false := by
  simp only [hasQuorum]
  have hne' : voteResult voters (quorumVotes ∅) ≠ VoteResult.Won := by
    rw [voteResult_won_iff (by exact_mod_cast Finset.card_ne_zero.mp hne)]
    rw [yesCount_quorumVotes_inter]
    simp [majority, hne]
    omega
  simp [hne']

/-! ## PROP-6: Explicit count characterization -/

/-- PROP-6: `hasQuorum voters potQuorum ↔ |(voters ∩ potQuorum)| ≥ majority(|voters|)`
    for non-empty voter sets. -/
theorem hasQuorum_count_iff (voters potQuorum : Finset Nat) (hne : voters.card ≠ 0) :
    hasQuorum voters potQuorum = true ↔
    (voters ∩ potQuorum).card ≥ majority voters.card := by
  simp only [hasQuorum, Bool.beq_eq_true_iff]
  rw [voteResult_won_iff (by exact_mod_cast Finset.card_ne_zero.mp hne)]
  rw [yesCount_quorumVotes_inter]

/-! ## PROP-7: Full voter set forms a quorum -/

/-- PROP-7: `hasQuorum voters voters = true` whenever `voters ≠ ∅`. -/
theorem hasQuorum_full (voters : Finset Nat) (hne : voters.card ≠ 0) :
    hasQuorum voters voters = true := by
  rw [hasQuorum_count_iff voters voters hne]
  simp [Finset.inter_self, majority]
  omega

/-! ## PROP-8: Monotonicity -/

/-- PROP-8: **Monotonicity** (superset-closure): if `S` is a quorum and `T ⊇ S`,
    then `T` is also a quorum. -/
theorem hasQuorum_mono (voters : Finset Nat) {S T : Finset Nat} (hST : S ⊆ T)
    (h : hasQuorum voters S = true) : hasQuorum voters T = true := by
  by_cases hne : voters.card = 0
  · simp [hasQuorum, voteResult, hne]
  · rw [hasQuorum_count_iff _ _ hne] at h ⊢
    apply le_trans h
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_inter] at hx ⊢
    exact ⟨hx.1, hST hx.2⟩

/-! ## PROP-9: Singleton voter config -/

/-- PROP-9: Singleton voter config: `hasQuorum` iff the single voter is in `potQuorum`. -/
theorem hasQuorum_singleton (v : Nat) (potQuorum : Finset Nat) :
    hasQuorum {v} potQuorum = decide (v ∈ potQuorum) := by
  by_cases hmem : v ∈ potQuorum
  · have htrue : decide (v ∈ potQuorum) = true := decide_eq_true hmem
    rw [htrue, hasQuorum_count_iff _ _ (by simp)]
    have hinter : {v} ∩ potQuorum = {v} := by
      ext w; simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · exact And.left
      · intro heq; exact ⟨heq, heq ▸ hmem⟩
    simp [hinter, majority]
  · have hfalse : decide (v ∈ potQuorum) = false := decide_eq_false hmem
    rw [hfalse]
    simp only [hasQuorum]
    have hne' : voteResult {v} (quorumVotes potQuorum) ≠ VoteResult.Won := by
      rw [voteResult_won_iff (by simp)]
      rw [yesCount_quorumVotes_inter]
      have hinter : {v} ∩ potQuorum = ∅ := by
        ext w; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.not_mem_empty,
                          iff_false, not_and]
        intro heq; exact heq ▸ hmem
      simp [hinter, majority]
    simp [hne']

/-! ## PROP-10: Disjoint quorums must overlap -/

/-- PROP-10: The combined intersection sizes of two quorums exceed the voter count.
    This is the arithmetic form of quorum intersection: since each quorum covers
    a majority, their union must overlap by the pigeonhole principle.
    Consequence: any two quorums share at least one common voter. -/
theorem hasQuorum_intersection_sum (voters : Finset Nat) (S T : Finset Nat)
    (hS : hasQuorum voters S = true) (hT : hasQuorum voters T = true)
    (hne : voters.card ≠ 0) :
    (voters ∩ S).card + (voters ∩ T).card > voters.card := by
  rw [hasQuorum_count_iff _ _ hne] at hS hT
  have h := quorum_intersection voters (quorumVotes S) (quorumVotes T)
    (by rwa [← yesCount_quorumVotes_inter])
    (by rwa [← yesCount_quorumVotes_inter]) hne
  simp only [yesCount_quorumVotes_inter] at h
  exact h

/-! ## PROP-11: grantedCount is a lower bound for voteResult Won -/

/-- PROP-11: If `grantedCount ≥ majority(|voters|)`, the vote result is Won. -/
theorem voteResult_won_of_granted (voters : Finset Nat) (votes : VoteMap)
    (hne : voters.card ≠ 0)
    (hg : grantedCount voters votes ≥ majority voters.card) :
    voteResult voters votes = VoteResult.Won := by
  rw [voteResult_won_iff (by exact_mod_cast Finset.card_ne_zero.mp hne)]
  rwa [← grantedCount_eq_yesCount]

/-- PROP-12: If `rejected ≥ majority(|voters|)`, the vote result is Lost. -/
theorem voteResult_lost_of_rejected (voters : Finset Nat) (votes : VoteMap)
    (hne : voters.card ≠ 0)
    (hr : rejectedCount voters votes ≥ majority voters.card) :
    voteResult voters votes = VoteResult.Lost := by
  rw [voteResult_lost_iff (by exact_mod_cast Finset.card_ne_zero.mp hne)]
  -- We need: yesCount + missingCount < majority
  -- From the partition: granted + rejected + pending = voters.card
  -- With rejected ≥ majority and 2*majority > voters.card → granted + pending < majority
  have hpart := tally_partition voters votes
  rw [grantedCount_eq_yesCount, pendingCount_eq_missingCount] at hpart
  have hmaj := majority_gt_half voters.card
  omega

/-! ## Decision examples (concrete verification via kernel reduction) -/

-- Example 1: 2 yes out of 3 voters → (2, 0, Won)
#eval tallyVotes {1, 2, 3} (fun v => match v with | 1 => some true | 2 => some true | _ => none)

-- Example 2: 2 no out of 3 voters → (0, 2, Lost)
#eval tallyVotes {1, 2, 3} (fun v => match v with | 1 => some false | 2 => some false | _ => none)

-- Example 3: No votes → (0, 0, Pending)
#eval tallyVotes {1, 2, 3} (fun _ => none)

-- Example 4: Empty voters → (0, 0, Won)
#eval tallyVotes (∅ : Finset Nat) (fun _ => none)

-- Example 5: Non-voter vote ignored (voter 99 not in {1,2,3})
#eval (grantedCount {1, 2, 3} (fun v => if v = 99 then some true else none),
       grantedCount {1, 2, 3} (fun _ => none))  -- both should be 0

-- hasQuorum examples
#eval hasQuorum {1, 2, 3} {1, 2}    -- true  (2 ≥ majority(3) = 2)
#eval hasQuorum {1, 2, 3} {1}       -- false (1 < 2)
#eval hasQuorum {1, 2, 3} ∅         -- false
#eval hasQuorum (∅ : Finset Nat) ∅  -- true  (empty config wins)

end FVSquad.TallyVotes
