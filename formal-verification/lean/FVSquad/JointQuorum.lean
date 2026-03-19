/-!
# Joint Quorum — Lean 4 Specification

Formal specification of `JointConfig::vote_result` and `JointConfig::committed_index`
from `raft-rs` (`src/quorum/joint.rs`).

## Model scope and approximations

* **Types**: Voter IDs are `Nat` (Rust uses `u64`; overflow not relevant to these properties).
* **`JointConfig`**: two `Finset Nat` (incoming and outgoing voter sets).
* **`jointVoteResult`**: exact functional model of `Configuration::vote_result` in joint.rs.
  Composes `voteResult` from `MajorityQuorum` (imported).
* **`jointCommittedIndex`**: modelled as `min i_idx o_idx` — exact translation of
  `cmp::min(i_idx, o_idx)` in the Rust implementation.
* **Empty-config handling**: Rust's empty config returns `(u64::MAX, true)`; in this model,
  when voters is empty `voteResult ∅ check = VoteResult.Won` (from MajorityQuorum) and
  the joint committed equals the other config's value (min with ∞).
* **Omitted**: `use_group_commit` flag, group commit algorithm, `AckedIndexer` trait,
  protobuf I/O, membership change protocol, configuration transitions.

🔬 *Lean Squad — auto-generated formal specification.*

-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import FVSquad.MajorityQuorum

namespace FVSquad.JointQuorum

open FVSquad.MajorityQuorum

/-! ## JointConfig type -/

/-- A joint configuration during a Raft membership change.
    Decisions require the support of *both* majority quorums.
    When `outgoing` is empty the configuration behaves as a simple majority. -/
structure JointConfig where
  incoming : Finset Nat
  outgoing : Finset Nat
  deriving Repr

/-! ## `jointVoteResult` -/

/-- `jointVoteResult cfg check` — functional model of `Configuration::vote_result` in
    `src/quorum/joint.rs`.

    A joint vote is:
    - **Won** iff *both* majority configs vote Won.
    - **Lost** iff *either* majority config votes Lost (i.e. cannot possibly win there).
    - **Pending** otherwise (waiting for more votes). -/
def jointVoteResult (cfg : JointConfig) (check : VoteAssignment) : VoteResult :=
  let i := voteResult cfg.incoming check
  let o := voteResult cfg.outgoing check
  match i, o with
  | VoteResult.Won,  VoteResult.Won  => VoteResult.Won
  | VoteResult.Lost, _               => VoteResult.Lost
  | _,               VoteResult.Lost => VoteResult.Lost
  | _,               _               => VoteResult.Pending

/-! ## `jointCommittedIndex` -/

/-- `jointCommittedIndex i_idx o_idx` is the joint committed index: the minimum of the
    two majority committed indexes.
    Models `cmp::min(i_idx, o_idx)` in `Configuration::committed_index`. -/
def jointCommittedIndex (i_idx o_idx : Nat) : Nat := min i_idx o_idx

/-! ## Sanity checks -/

-- Example: joint config {1, 2, 3} incoming, {1, 2} outgoing, all vote yes.
private def exCfg : JointConfig :=
  { incoming := {1, 2, 3}, outgoing := {1, 2} }
private def exCheckAllYes : VoteAssignment := fun _ => some true
private def exCheckNone   : VoteAssignment := fun _ => none

#eval jointVoteResult exCfg exCheckAllYes  -- Won
#eval jointVoteResult exCfg exCheckNone    -- Pending
#eval jointCommittedIndex 5 3              -- 3
#eval jointCommittedIndex 3 5              -- 3
#eval jointCommittedIndex 0 100            -- 0

/-! ## Key properties of `jointVoteResult` -/

/-- A joint vote is Won iff *both* constituent majorities vote Won. -/
theorem jointVoteResult_won_iff (cfg : JointConfig) (check : VoteAssignment) :
    jointVoteResult cfg check = VoteResult.Won ↔
    voteResult cfg.incoming check = VoteResult.Won ∧
    voteResult cfg.outgoing check = VoteResult.Won := by
  simp only [jointVoteResult]
  cases voteResult cfg.incoming check <;> cases voteResult cfg.outgoing check <;> simp

/-- A joint vote is Lost iff *either* constituent majority votes Lost. -/
theorem jointVoteResult_lost_iff (cfg : JointConfig) (check : VoteAssignment) :
    jointVoteResult cfg check = VoteResult.Lost ↔
    voteResult cfg.incoming check = VoteResult.Lost ∨
    voteResult cfg.outgoing check = VoteResult.Lost := by
  simp only [jointVoteResult]
  cases voteResult cfg.incoming check <;> cases voteResult cfg.outgoing check <;> simp

/-- A joint vote is Pending iff neither side has lost and they haven't both won. -/
theorem jointVoteResult_pending_iff (cfg : JointConfig) (check : VoteAssignment) :
    jointVoteResult cfg check = VoteResult.Pending ↔
    (voteResult cfg.incoming check ≠ VoteResult.Won ∨
     voteResult cfg.outgoing check ≠ VoteResult.Won) ∧
    voteResult cfg.incoming check ≠ VoteResult.Lost ∧
    voteResult cfg.outgoing check ≠ VoteResult.Lost := by
  simp only [jointVoteResult]
  cases voteResult cfg.incoming check <;> cases voteResult cfg.outgoing check <;> simp

/-- Won and Lost are mutually exclusive for joint vote. -/
theorem jointVoteResult_won_ne_lost (cfg : JointConfig) (check : VoteAssignment)
    (h : jointVoteResult cfg check = VoteResult.Won) :
    jointVoteResult cfg check ≠ VoteResult.Lost := by
  simp [h]

/-- If the joint vote is Won, the incoming majority voted Won. -/
theorem jointVoteResult_won_incoming (cfg : JointConfig) (check : VoteAssignment)
    (h : jointVoteResult cfg check = VoteResult.Won) :
    voteResult cfg.incoming check = VoteResult.Won :=
  ((jointVoteResult_won_iff cfg check).mp h).1

/-- If the joint vote is Won, the outgoing majority voted Won. -/
theorem jointVoteResult_won_outgoing (cfg : JointConfig) (check : VoteAssignment)
    (h : jointVoteResult cfg check = VoteResult.Won) :
    voteResult cfg.outgoing check = VoteResult.Won :=
  ((jointVoteResult_won_iff cfg check).mp h).2

/-- If the incoming majority voted Lost, the joint vote is Lost. -/
theorem jointVoteResult_lost_of_incoming (cfg : JointConfig) (check : VoteAssignment)
    (h : voteResult cfg.incoming check = VoteResult.Lost) :
    jointVoteResult cfg check = VoteResult.Lost := by
  rw [jointVoteResult_lost_iff]; left; exact h

/-- If the outgoing majority voted Lost, the joint vote is Lost. -/
theorem jointVoteResult_lost_of_outgoing (cfg : JointConfig) (check : VoteAssignment)
    (h : voteResult cfg.outgoing check = VoteResult.Lost) :
    jointVoteResult cfg check = VoteResult.Lost := by
  rw [jointVoteResult_lost_iff]; right; exact h

/-! ## Empty-config simplifications -/

/-- With an empty outgoing config (simple majority case), the joint vote equals
    the incoming majority vote. -/
theorem jointVoteResult_empty_outgoing (incoming : Finset Nat) (check : VoteAssignment) :
    jointVoteResult ⟨incoming, ∅⟩ check = voteResult incoming check := by
  simp only [jointVoteResult, voteResult_empty]
  cases voteResult incoming check <;> simp

/-- With an empty incoming config (empty majority), the joint vote is
    determined by the outgoing config. -/
theorem jointVoteResult_empty_incoming (outgoing : Finset Nat) (check : VoteAssignment) :
    jointVoteResult ⟨∅, outgoing⟩ check = voteResult outgoing check := by
  simp only [jointVoteResult, voteResult_empty]
  cases voteResult outgoing check <;> simp

/-- When both configs are empty, the joint vote is Won. -/
theorem jointVoteResult_empty_both (check : VoteAssignment) :
    jointVoteResult ⟨∅, ∅⟩ check = VoteResult.Won := by
  simp [jointVoteResult, voteResult_empty]

/-! ## Key properties of `jointCommittedIndex` -/

/-- `jointCommittedIndex` is symmetric (min is commutative). -/
theorem jointCommittedIndex_comm (a b : Nat) :
    jointCommittedIndex a b = jointCommittedIndex b a := by
  simp [jointCommittedIndex, Nat.min_comm]

/-- The joint committed index is at most the incoming committed index. -/
theorem jointCommittedIndex_le_left (a b : Nat) :
    jointCommittedIndex a b ≤ a := by
  simp [jointCommittedIndex]

/-- The joint committed index is at most the outgoing committed index. -/
theorem jointCommittedIndex_le_right (a b : Nat) :
    jointCommittedIndex a b ≤ b := by
  simp [jointCommittedIndex]

/-- The joint committed index equals the minimum of its arguments. -/
theorem jointCommittedIndex_eq_min (a b : Nat) :
    jointCommittedIndex a b = min a b :=
  rfl

/-- `jointCommittedIndex` is monotone in its left argument. -/
theorem jointCommittedIndex_mono_left {a a' b : Nat} (h : a ≤ a') :
    jointCommittedIndex a b ≤ jointCommittedIndex a' b := by
  simp [jointCommittedIndex]; omega

/-- `jointCommittedIndex` is monotone in its right argument. -/
theorem jointCommittedIndex_mono_right {a b b' : Nat} (h : b ≤ b') :
    jointCommittedIndex a b ≤ jointCommittedIndex a b' := by
  simp [jointCommittedIndex]; omega

/-- `jointCommittedIndex` is bounded below by 0. -/
theorem jointCommittedIndex_nonneg (a b : Nat) : 0 ≤ jointCommittedIndex a b := by
  simp [jointCommittedIndex]

/-- `jointCommittedIndex` equals the left argument if it is smaller. -/
theorem jointCommittedIndex_eq_left {a b : Nat} (h : a ≤ b) :
    jointCommittedIndex a b = a := by
  simp [jointCommittedIndex, Nat.min_eq_left h]

/-- `jointCommittedIndex` equals the right argument if it is smaller. -/
theorem jointCommittedIndex_eq_right {a b : Nat} (h : b ≤ a) :
    jointCommittedIndex a b = b := by
  simp [jointCommittedIndex, Nat.min_eq_right h]

/-- If both committed indexes are equal, the joint committed index equals that value. -/
theorem jointCommittedIndex_eq_of_eq {a b : Nat} (h : a = b) :
    jointCommittedIndex a b = a := by
  simp [jointCommittedIndex, h]

/-- The joint committed index is the greatest lower bound: it is the largest value
    that is ≤ both arguments. -/
theorem jointCommittedIndex_greatest_lb {c a b : Nat} (ha : c ≤ a) (hb : c ≤ b) :
    c ≤ jointCommittedIndex a b := by
  simp [jointCommittedIndex]; omega

/-- In the degenerate single-config case (outgoing empty), the effective committed
    index is just the incoming committed index.  When we model empty config as
    contributing ⊤ (infinity), we have: min a ∞ = a.
    Concretely: for any sentinel M ≥ a, jointCommittedIndex a M = a. -/
theorem jointCommittedIndex_single_config (a M : Nat) (hM : a ≤ M) :
    jointCommittedIndex a M = a :=
  jointCommittedIndex_eq_left hM

/-! ## Safety theorem: joint quorum stricter than single quorum -/

/-- A joint quorum commit cannot exceed the commit of either individual quorum.
    This formalises the key safety property: the joint configuration is *stricter*
    than either constituent quorum. -/
theorem jointCommittedIndex_safety (i_idx o_idx : Nat) :
    jointCommittedIndex i_idx o_idx ≤ i_idx ∧
    jointCommittedIndex i_idx o_idx ≤ o_idx :=
  ⟨jointCommittedIndex_le_left i_idx o_idx,
   jointCommittedIndex_le_right i_idx o_idx⟩

/-- A joint vote Won is the *strongest* positive outcome: if Won under a joint
    config, then Won under each constituent majority individually. -/
theorem jointVoteResult_won_implies_each (cfg : JointConfig) (check : VoteAssignment)
    (h : jointVoteResult cfg check = VoteResult.Won) :
    voteResult cfg.incoming check = VoteResult.Won ∧
    voteResult cfg.outgoing check = VoteResult.Won :=
  (jointVoteResult_won_iff cfg check).mp h

/-- Lost is monotone: if the joint vote is not Lost but individual incoming lost,
    then by the iff this means incoming ≠ Lost — a consistency check. -/
theorem jointVoteResult_not_lost_incoming (cfg : JointConfig) (check : VoteAssignment)
    (h : jointVoteResult cfg check ≠ VoteResult.Lost) :
    voteResult cfg.incoming check ≠ VoteResult.Lost := by
  intro hi
  exact h (jointVoteResult_lost_of_incoming cfg check hi)

/-- If joint is not Lost, outgoing is not Lost either. -/
theorem jointVoteResult_not_lost_outgoing (cfg : JointConfig) (check : VoteAssignment)
    (h : jointVoteResult cfg check ≠ VoteResult.Lost) :
    voteResult cfg.outgoing check ≠ VoteResult.Lost := by
  intro ho
  exact h (jointVoteResult_lost_of_outgoing cfg check ho)

end FVSquad.JointQuorum
