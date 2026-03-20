/-!
# Quorum Recently Active — Lean 4 Specification

Formal specification of `ProgressTracker::quorum_recently_active` from `raft-rs`
(`src/tracker.rs`).

## What this function does

`quorum_recently_active(perspective_of)` is the heart of Raft's **Check Quorum**
mechanism. A leader calls it periodically to verify that a quorum of voters has
communicated with it recently. If not, the leader steps down voluntarily to avoid
split-brain in a network partition.

The function:
1. Marks `perspective_of` (the caller / leader) as *always* active (self-inclusion)
2. Collects all other peers whose `recent_active` flag is `true` into the active set
3. Resets all `recent_active` flags to `false`, except for `perspective_of` (set to `true`)
4. Returns whether the active set forms a quorum according to the voter configuration

## Model scope and approximations

* **Types**: Node IDs are `Nat` (Rust uses `u64`; overflow is irrelevant here).
* **Voter configuration**: modelled as a single `Finset Nat` (majority quorum).
  The actual implementation uses `JointConfig` (two majority sets); this model
  captures the single-config case. Monotonicity results hold for joint quorums too.
* **recent_active flags**: modelled as a function `Nat → Bool` over all IDs.
  In Rust this is a field on each `Progress` struct in a `HashMap`.
* **Peers / learners**: We model `activeSet` filtered over `voters` only.
  In Rust, learners may appear in `active`, but `has_quorum` uses `voters.vote_result`
  which ignores non-voter IDs, so learner presence does not affect the result.
* **Omitted**: joint quorum details, learner handling, other `Progress` fields,
  concurrent access, protobuf I/O.

🔬 *Lean Squad — auto-generated formal specification.*

-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import FVSquad.MajorityQuorum

namespace FVSquad.QuorumRecentlyActive

open FVSquad.MajorityQuorum

/-! ## State structure -/

/-- Abstract state of the progress tracker, containing the voter set and
    the `recent_active` flags for all peers. -/
structure QRAState where
  /-- The set of voting peers (majority quorum model). -/
  voters       : Finset Nat
  /-- Per-peer `recent_active` flag (state *before* a call). -/
  recentActive : Nat → Bool

/-! ## Core definitions -/

/-- The set of voters that are considered "active" from `perspOf`'s viewpoint.
    Mirrors the `active` `HashSet` built in `quorum_recently_active`.
    An ID is active iff it equals `perspOf` (self always active) or its
    `recentActive` flag is `true`. -/
def activeSet (s : QRAState) (perspOf : Nat) : Finset Nat :=
  s.voters.filter (fun id => id == perspOf || s.recentActive id)

/-- Check whether `active` constitutes a quorum, by calling `voteResult` with
    `some true` for IDs in the active set and `none` for the rest.
    Mirrors `has_quorum` in `src/tracker.rs`. -/
def hasQuorum (voters : Finset Nat) (active : Finset Nat) : Bool :=
  voteResult voters (fun id => if id ∈ active then some true else none) == VoteResult.Won

/-- The pure functional model of `quorum_recently_active`.
    Returns `(result, new_state)` where `new_state` has `perspOf.recentActive = true`
    and all other peers reset to `false`. -/
def quorumRecentlyActive (s : QRAState) (perspOf : Nat) : Bool × QRAState :=
  let active := activeSet s perspOf
  let result := hasQuorum s.voters active
  let newRA  := fun (id : Nat) => id == perspOf   -- self: true; others: false
  (result, { voters := s.voters, recentActive := newRA })

/-! ## Helper lemma: yesCount for membership check -/

/-- The `yesCount` for the membership-based assignment equals the filter cardinality. -/
private lemma yesCount_mem_filter (voters active : Finset Nat) :
    yesCount voters (fun id => if id ∈ active then some true else none) =
    (voters.filter (fun id => id ∈ active)).card := by
  simp only [yesCount]
  congr 1
  ext id
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hv, heq⟩
    split_ifs at heq with h
    · exact ⟨hv, h⟩
    · simp at heq
  · intro ⟨hv, hmem⟩
    exact ⟨hv, by simp [hmem]⟩

/-! ## Helper lemma: hasQuorum via filter cardinality -/

/-- `hasQuorum voters active = true` iff the number of active voters ≥ majority. -/
theorem hasQuorum_iff (voters active : Finset Nat) (hne : voters.card ≠ 0) :
    hasQuorum voters active = true ↔
    majority voters.card ≤ (voters.filter (fun id => id ∈ active)).card := by
  simp only [hasQuorum, Bool.beq_eq_true_iff, ge_iff_le]
  rw [voteResult_won_iff _ _ hne, yesCount_mem_filter]

/-- Empty voters always gives a quorum (base case). -/
theorem hasQuorum_empty_voters (active : Finset Nat) :
    hasQuorum ∅ active = true := by
  simp [hasQuorum, voteResult_empty]

/-! ## PROP-1: Self-inclusion -/

/-- PROP-1: If `perspOf` is a voter, it is always in `activeSet`. -/
theorem activeSet_mem_self (s : QRAState) (perspOf : Nat)
    (hmem : perspOf ∈ s.voters) : perspOf ∈ activeSet s perspOf := by
  simp [activeSet, Finset.mem_filter, hmem]

/-! ## PROP-2: Active set membership characterization -/

/-- PROP-2: A voter `id` is in `activeSet` iff it equals `perspOf` or is recently active. -/
theorem mem_activeSet_iff (s : QRAState) (perspOf id : Nat) :
    id ∈ activeSet s perspOf ↔
    id ∈ s.voters ∧ (id = perspOf ∨ s.recentActive id = true) := by
  simp [activeSet, Finset.mem_filter, beq_iff_eq, Bool.or_eq_true]

/-- PROP-2b: A non-self voter is active iff its `recentActive` flag is set. -/
theorem mem_activeSet_non_self (s : QRAState) (perspOf id : Nat)
    (hne : id ≠ perspOf) (hmem : id ∈ s.voters) :
    id ∈ activeSet s perspOf ↔ s.recentActive id = true := by
  rw [mem_activeSet_iff]
  simp [hmem, hne]

/-! ## PROP-3: Active set is a subset of voters -/

/-- PROP-3: `activeSet s perspOf ⊆ s.voters`. -/
theorem activeSet_subset (s : QRAState) (perspOf : Nat) :
    activeSet s perspOf ⊆ s.voters :=
  Finset.filter_subset _ _

/-! ## PROP-4: Return value characterization -/

/-- PROP-4: The return value is `true` iff the active set forms a quorum. -/
theorem quorumRecentlyActive_result_iff (s : QRAState) (perspOf : Nat) :
    (quorumRecentlyActive s perspOf).1 = true ↔
    hasQuorum s.voters (activeSet s perspOf) = true := by
  simp [quorumRecentlyActive]

/-! ## PROP-5: Post-state — self is active -/

/-- PROP-5: After the call, `perspOf`'s `recentActive` flag is `true`. -/
theorem newState_self_active (s : QRAState) (perspOf : Nat) :
    (quorumRecentlyActive s perspOf).2.recentActive perspOf = true := by
  simp [quorumRecentlyActive]

/-! ## PROP-6: Post-state — all others are reset -/

/-- PROP-6: After the call, every peer other than `perspOf` has `recentActive = false`. -/
theorem newState_others_inactive (s : QRAState) (perspOf id : Nat)
    (hne : id ≠ perspOf) :
    (quorumRecentlyActive s perspOf).2.recentActive id = false := by
  simp [quorumRecentlyActive, beq_iff_eq, hne]

/-! ## PROP-7: Post-state — voters unchanged -/

/-- PROP-7: The voter configuration is not modified by the call. -/
theorem newState_voters_unchanged (s : QRAState) (perspOf : Nat) :
    (quorumRecentlyActive s perspOf).2.voters = s.voters := by
  simp [quorumRecentlyActive]

/-! ## PROP-8: Second call's active set contains only perspOf -/

/-- PROP-8: After one call, the active set for an immediate second call equals
    `{perspOf} ∩ voters` (only self remains active). -/
theorem second_call_activeSet (s : QRAState) (perspOf : Nat) :
    activeSet (quorumRecentlyActive s perspOf).2 perspOf =
    s.voters.filter (fun id => id = perspOf) := by
  simp only [quorumRecentlyActive, activeSet]
  ext id
  simp only [Finset.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨hv, hself | hact⟩
    · exact ⟨hv, hself⟩
    · exact ⟨hv, hact⟩
  · rintro ⟨hv, hself⟩
    exact ⟨hv, Or.inl hself⟩

/-! ## PROP-9: Second call result depends only on whether self is a solo quorum -/

/-- PROP-9: After one call, a second call returns `true` iff `perspOf` alone
    is a quorum (i.e., majority(|voters|) ≤ 1, which means |voters| ≤ 2 or
    |voters ∩ {perspOf}| ≥ majority). -/
theorem second_call_result_iff (s : QRAState) (perspOf : Nat) :
    let s2 := (quorumRecentlyActive s perspOf).2
    (quorumRecentlyActive s2 perspOf).1 = true ↔
    hasQuorum s.voters (s.voters.filter (fun id => id = perspOf)) = true := by
  simp only []
  constructor
  · intro h
    have heq := second_call_activeSet s perspOf
    rw [quorumRecentlyActive_result_iff] at h
    rw [← heq]
    rw [← quorumRecentlyActive_result_iff]
    convert h using 2
    simp [quorumRecentlyActive]
  · intro h
    rw [quorumRecentlyActive_result_iff]
    rw [second_call_activeSet]
    simp only [quorumRecentlyActive, newState_voters_unchanged]
    exact h

/-! ## PROP-10: Single-voter cluster always returns true -/

/-- PROP-10: If the only voter is `perspOf` itself, the call always returns `true`. -/
theorem single_voter_always_true (s : QRAState) (perspOf : Nat)
    (hsingle : s.voters = {perspOf}) :
    (quorumRecentlyActive s perspOf).1 = true := by
  rw [quorumRecentlyActive_result_iff, hsingle]
  -- activeSet {voters := {perspOf}, ..} perspOf ⊇ {perspOf}
  have hmem : perspOf ∈ activeSet { voters := {perspOf}, recentActive := s.recentActive } perspOf :=
    activeSet_mem_self _ perspOf (Finset.mem_singleton_self _)
  have hsub : activeSet { voters := {perspOf}, recentActive := s.recentActive } perspOf ⊆ {perspOf} :=
    hsingle ▸ activeSet_subset _ perspOf
  have heq : activeSet { voters := {perspOf}, recentActive := s.recentActive } perspOf = {perspOf} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem)
  rw [heq]
  simp only [hasQuorum, Bool.beq_eq_true_iff]
  rw [voteResult_won_iff _ _ (by simp [Finset.card_singleton])]
  simp [yesCount, majority, Finset.card_singleton, Finset.filter_singleton,
        Finset.mem_singleton]

/-! ## PROP-11: Empty voter set always returns true -/

/-- PROP-11: An empty voter set always returns `true` (empty quorum wins by convention). -/
theorem empty_voters_always_true (s : QRAState) (perspOf : Nat)
    (hemp : s.voters = ∅) :
    (quorumRecentlyActive s perspOf).1 = true := by
  simp [quorumRecentlyActive, hemp, hasQuorum_empty_voters, activeSet]

/-! ## PROP-12: Active set cardinality lower bound -/

/-- PROP-12: If `perspOf ∈ voters`, then `|activeSet| ≥ 1`. -/
theorem activeSet_card_pos (s : QRAState) (perspOf : Nat)
    (hmem : perspOf ∈ s.voters) :
    0 < (activeSet s perspOf).card :=
  Finset.card_pos.mpr ⟨perspOf, activeSet_mem_self s perspOf hmem⟩

/-! ## PROP-13: hasQuorum is monotone in the active set -/

/-- PROP-13: If `active1 ⊆ active2` and `hasQuorum voters active1 = true`,
    then `hasQuorum voters active2 = true`. -/
theorem hasQuorum_mono (voters active1 active2 : Finset Nat)
    (hne : voters.card ≠ 0)
    (hsub : active1 ⊆ active2)
    (hq  : hasQuorum voters active1 = true) :
    hasQuorum voters active2 = true := by
  rw [hasQuorum_iff _ _ hne] at hq ⊢
  apply le_trans hq
  apply Finset.card_le_card
  intro id hid
  simp only [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, hsub hid.2⟩

/-! ## PROP-14: quorumRecentlyActive is monotone in recentActive flags -/

/-- PROP-14: If `s2.recentActive` dominates `s1.recentActive` (more nodes active)
    and the same voters, and `quorumRecentlyActive s1 perspOf = true`, then
    `quorumRecentlyActive s2 perspOf = true`. -/
theorem quorumRecentlyActive_mono
    (s1 s2 : QRAState) (perspOf : Nat)
    (hv   : s1.voters = s2.voters)
    (hne  : s1.voters.card ≠ 0)
    (hRA  : ∀ id, s1.recentActive id = true → s2.recentActive id = true)
    (h1   : (quorumRecentlyActive s1 perspOf).1 = true) :
    (quorumRecentlyActive s2 perspOf).1 = true := by
  rw [quorumRecentlyActive_result_iff] at h1 ⊢
  apply hasQuorum_mono s1.voters (activeSet s1 perspOf) (activeSet s2 perspOf)
    (hv ▸ hne) _ h1
  intro id hid
  rw [mem_activeSet_iff] at hid ⊢
  obtain ⟨hv1, hor⟩ := hid
  refine ⟨hv ▸ hv1, ?_⟩
  rcases hor with rfl | hact
  · exact Or.inl rfl
  · exact Or.inr (hRA id hact)

/-! ## PROP-15: Post-state is independent of old recentActive flags -/

/-- PROP-15: The post-call state depends only on `s.voters` and `perspOf`,
    not on `s.recentActive`. The flags are fully reset regardless of prior state. -/
theorem newState_canonical (s1 s2 : QRAState) (perspOf : Nat)
    (hv : s1.voters = s2.voters) :
    (quorumRecentlyActive s1 perspOf).2 = (quorumRecentlyActive s2 perspOf).2 := by
  simp [quorumRecentlyActive, hv]

/-! ## Examples validated by native_decide -/

section Examples

/-- Example: 3-node cluster, 2 active (self + peer 1) → quorum → true. -/
example : hasQuorum ({0, 1, 2} : Finset Nat) ({0, 1} : Finset Nat) = true := by
  native_decide

/-- Example: 3-node cluster, only self active → no quorum → false. -/
example : hasQuorum ({0, 1, 2} : Finset Nat) ({0} : Finset Nat) = false := by
  native_decide

/-- Example: 5-node cluster, 3 active → quorum → true. -/
example : hasQuorum ({0, 1, 2, 3, 4} : Finset Nat) ({0, 1, 2} : Finset Nat) = true := by
  native_decide

/-- Example: 5-node cluster, 2 active → no quorum → false. -/
example : hasQuorum ({0, 1, 2, 3, 4} : Finset Nat) ({0, 1} : Finset Nat) = false := by
  native_decide

/-- Full pipeline: 3-node cluster, peer 1 recently active, returns true. -/
example : (quorumRecentlyActive
    { voters := {0, 1, 2}, recentActive := fun id => id == 1 } 0).1 = true := by
  native_decide

/-- Full pipeline: 3-node cluster, no peers recently active, returns false. -/
example : (quorumRecentlyActive
    { voters := {0, 1, 2}, recentActive := fun _ => false } 0).1 = false := by
  native_decide

/-- Second call: after a true call, second call in 1-of-3 is false. -/
example : let s := { voters := ({0, 1, 2} : Finset Nat),
                      recentActive := fun id => id == (1 : Nat) }
          let (_, s2) := quorumRecentlyActive s 0
          (quorumRecentlyActive s2 0).1 = false := by
  native_decide

end Examples

end FVSquad.QuorumRecentlyActive
