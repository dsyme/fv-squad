import FVSquad.MajorityVote

/-!
# Formal Specification: `Configuration::vote_result` (Joint Quorum)

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises `Configuration::vote_result` from `src/quorum/joint.rs`.
It builds directly on `FVSquad.MajorityVote` (the majority-quorum model).

## What `joint vote_result` does

```rust
pub fn vote_result(&self, check: impl Fn(u64) -> Option<bool>) -> VoteResult {
    let i = self.incoming.vote_result(&check);
    let o = self.outgoing.vote_result(check);
    match (i, o) {
        (VoteResult::Won, VoteResult::Won) => VoteResult::Won,
        (VoteResult::Lost, _) | (_, VoteResult::Lost) => VoteResult::Lost,
        _ => VoteResult::Pending,
    }
}
```

A joint quorum wins only if **both** constituent majority quorums win.
It loses if **either** constituent quorum loses.
Otherwise it is pending.

Key note: `outgoing` is empty in a non-joint configuration. `voteResult [] check = Won`
(the `MajorityVote` convention), so in a non-joint config `jointVoteResult` degenerates
to whatever the incoming quorum returns — exactly the desired behaviour.

## Modelling choices

- Inherits `VoteResult`, `majority`, `yesCount`, `missingCount`, `voteResult` from
  `FVSquad.MajorityVote`.
- `JointConfig` is modelled as a pair of `List Nat` (incoming and outgoing voters).
- The same abstractions apply: `HashSet<u64>` → `List Nat`; `u64` → `Nat`.
-/

/-! ## Joint quorum combinator -/

/-- Combine two majority-quorum results into a joint-quorum result.
    Mirrors the `match` in `Configuration::vote_result` (`src/quorum/joint.rs:68`). -/
def combineVotes (i o : VoteResult) : VoteResult :=
  match i, o with
  | VoteResult.Won, VoteResult.Won  => VoteResult.Won
  | VoteResult.Lost, _              => VoteResult.Lost
  | _, VoteResult.Lost              => VoteResult.Lost
  | _, _                            => VoteResult.Pending

/-- Determine the vote result for a joint (two-group) quorum.
    Mirrors `Configuration::vote_result` in `src/quorum/joint.rs:63`. -/
def jointVoteResult
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool) : VoteResult :=
  combineVotes (voteResult incoming check) (voteResult outgoing check)

/-! ## Evaluations -/

section Eval
-- 3-voter incoming, all yes; empty outgoing → Won/Won → Won
#eval jointVoteResult [1,2,3] [] (fun _ => some true)
-- 3-voter incoming, majority yes; 2-voter outgoing, one pending → Won/Pending → Pending
#eval jointVoteResult [1,2,3] [4,5]
        (fun v => if v ≤ 2 then some true else none)
-- incoming loses; outgoing would win → Lost/Won → Lost
#eval jointVoteResult [1,2,3] [4,5]
        (fun v => if v = 4 then some true else if v = 5 then some true else some false)
-- both pending → Pending
#eval jointVoteResult [1,2,3] [4,5]
        (fun v => if v = 1 then some true else none)
end Eval

/-! ## Auxiliary lemmas for `combineVotes` -/

section CombineLemmas

/-- CL1: combineVotes is Won iff both are Won. -/
theorem combineVotes_Won_iff (i o : VoteResult) :
    combineVotes i o = VoteResult.Won ↔ i = VoteResult.Won ∧ o = VoteResult.Won := by
  cases i <;> cases o <;> simp [combineVotes]

/-- CL2: combineVotes is Lost iff at least one is Lost. -/
theorem combineVotes_Lost_iff (i o : VoteResult) :
    combineVotes i o = VoteResult.Lost ↔ i = VoteResult.Lost ∨ o = VoteResult.Lost := by
  cases i <;> cases o <;> simp [combineVotes]

/-- CL3: combineVotes is Pending iff neither Won–Won nor any Lost. -/
theorem combineVotes_Pending_iff (i o : VoteResult) :
    combineVotes i o = VoteResult.Pending ↔
    ¬(i = VoteResult.Won ∧ o = VoteResult.Won) ∧
    ¬(i = VoteResult.Lost ∨ o = VoteResult.Lost) := by
  cases i <;> cases o <;> simp [combineVotes]

/-- CL4: combineVotes is commutative up to Won/Lost symmetry:
    if neither side is Won, combineVotes is symmetric. -/
theorem combineVotes_symm_Lost (i o : VoteResult) :
    combineVotes i o = VoteResult.Lost ↔ combineVotes o i = VoteResult.Lost := by
  simp [combineVotes_Lost_iff, or_comm]

end CombineLemmas

/-! ## Key theorems for `jointVoteResult` -/

/-- J1: Joint Won iff both incoming and outgoing win. -/
theorem jointVoteResult_Won_iff
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool) :
    jointVoteResult incoming outgoing check = VoteResult.Won ↔
    voteResult incoming check = VoteResult.Won ∧
    voteResult outgoing check = VoteResult.Won := by
  simp [jointVoteResult, combineVotes_Won_iff]

/-- J2: Joint Lost iff incoming or outgoing loses. -/
theorem jointVoteResult_Lost_iff
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool) :
    jointVoteResult incoming outgoing check = VoteResult.Lost ↔
    voteResult incoming check = VoteResult.Lost ∨
    voteResult outgoing check = VoteResult.Lost := by
  simp [jointVoteResult, combineVotes_Lost_iff]

/-- J3: Joint Pending iff not both Won and not either Lost. -/
theorem jointVoteResult_Pending_iff
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool) :
    jointVoteResult incoming outgoing check = VoteResult.Pending ↔
    ¬(voteResult incoming check = VoteResult.Won ∧
      voteResult outgoing check = VoteResult.Won) ∧
    ¬(voteResult incoming check = VoteResult.Lost ∨
      voteResult outgoing check = VoteResult.Lost) := by
  simp [jointVoteResult, combineVotes_Pending_iff]

/-- J4: Non-joint (empty outgoing) degenerates to the incoming result. -/
theorem jointVoteResult_non_joint (incoming : List Nat) (check : Nat → Option Bool) :
    jointVoteResult incoming [] check = voteResult incoming check := by
  simp [jointVoteResult, combineVotes, voteResult_empty_is_Won]
  -- outgoing is empty → voteResult [] check = Won
  -- combineVotes r Won = r for all r except Won/Won → Won
  cases h : voteResult incoming check <;> simp

/-- J5: If incoming loses, joint loses regardless of outgoing. -/
theorem jointVoteResult_incoming_Lost
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool)
    (hi : voteResult incoming check = VoteResult.Lost) :
    jointVoteResult incoming outgoing check = VoteResult.Lost := by
  simp [jointVoteResult_Lost_iff, hi]

/-- J6: If outgoing loses, joint loses regardless of incoming. -/
theorem jointVoteResult_outgoing_Lost
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool)
    (ho : voteResult outgoing check = VoteResult.Lost) :
    jointVoteResult incoming outgoing check = VoteResult.Lost := by
  simp [jointVoteResult_Lost_iff, ho]

/-- J7: All voters yes → joint Won. -/
theorem jointVoteResult_all_yes
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool)
    (hall_in  : ∀ v ∈ incoming,  check v = some true)
    (hall_out : ∀ v ∈ outgoing, check v = some true) :
    jointVoteResult incoming outgoing check = VoteResult.Won := by
  rw [jointVoteResult_Won_iff]
  exact ⟨voteResult_all_yes incoming check hall_in,
         voteResult_all_yes outgoing check hall_out⟩

/-- J8: Joint result is one of Won, Pending, or Lost (exhaustive). -/
theorem jointVoteResult_exhaustive
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool) :
    jointVoteResult incoming outgoing check = VoteResult.Won ∨
    jointVoteResult incoming outgoing check = VoteResult.Pending ∨
    jointVoteResult incoming outgoing check = VoteResult.Lost := by
  simp [jointVoteResult]
  cases voteResult incoming check <;> cases voteResult outgoing check <;>
    simp [combineVotes]

/-- J9: Symmetry: swapping incoming/outgoing cannot change Won to not-Won. -/
theorem jointVoteResult_Won_symm
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool) :
    jointVoteResult incoming outgoing check = VoteResult.Won ↔
    jointVoteResult outgoing incoming check = VoteResult.Won := by
  simp [jointVoteResult_Won_iff, and_comm]

/-- J10: Symmetry: swapping incoming/outgoing cannot change Lost to not-Lost. -/
theorem jointVoteResult_Lost_symm
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool) :
    jointVoteResult incoming outgoing check = VoteResult.Lost ↔
    jointVoteResult outgoing incoming check = VoteResult.Lost := by
  simp [jointVoteResult_Lost_iff, or_comm]
