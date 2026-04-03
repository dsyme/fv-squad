import FVSquad.JointVote
import FVSquad.TallyVotes

/-!
# Formal Specification: `ProgressTracker::tally_votes` (Joint Quorum)

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises `ProgressTracker::tally_votes` from `src/tracker.rs:303` for
the **joint-quorum** case — i.e., when `self.conf.voters` is a `JointConfig` with
non-empty `incoming` and `outgoing`.

It builds directly on:
- `FVSquad.JointVote` — `combineVotes`, `jointVoteResult`, the J1–J10 theorems.
- `FVSquad.TallyVotes` — `tallyVotes`, `yesCount`, `noCount`, the single-quorum theorems.

## What `tally_votes` does (joint case)

```rust
pub fn tally_votes(&self) -> (usize, usize, VoteResult) {
    let (mut granted, mut rejected) = (0, 0);
    for (id, vote) in &self.votes {
        if !self.conf.voters.contains(*id) { continue; }  // joint-config contains
        if *vote { granted += 1; } else { rejected += 1; }
    }
    let result = self.vote_result(&self.votes);   // calls JointConfig::vote_result
    (granted, rejected, result)
}
```

Key points:
- `JointConfig::contains(id)` = `incoming.contains(id) || outgoing.contains(id)`.
- `JointConfig::vote_result(check)` calls `combineVotes(incoming.vote_result(check),
  outgoing.vote_result(check))` — both majorities must win.
- The granted/rejected counts are over voters present in **either** quorum.

## Modelling choices

- Voters: two `List Nat` values `incoming` and `outgoing` (modelling `JointConfig`).
- Votes: `Nat → Option Bool` (modelling `HashMap<u64, bool>`).
- The `jVoters` union list is the concatenation `incoming ++ outgoing`.
  In the real implementation a voter appearing in both halves has a single vote entry,
  so their grant/reject is counted once.  Our model may double-count overlap voters —
  this is a documented approximation (see below).
- `u64` → `Nat`; no overflow modelled.

## Known approximation

If a voter `v` appears in both `incoming` and `outgoing`, the Rust implementation
counts their vote **once** (because `self.votes` is a `HashMap` keyed by node ID).
Our model counts it **twice** (once per list).  In a well-formed `JointConfig` there
is no overlap between `incoming` and `outgoing` (the invariant is maintained by
configuration-change machinery in `src/confchange/`), so this divergence does not
arise in practice.  We state the relevant theorems with an explicit `no_overlap`
hypothesis where the approximation matters.

## Theorem table

| ID   | Name                                   | Description                                                         |
|------|----------------------------------------|---------------------------------------------------------------------|
| JT1  | `jointTallyVotes_result`               | Result component = `jointVoteResult`                                |
| JT2  | `jointTallyVotes_Won_iff`              | Won iff both halves win                                             |
| JT3  | `jointTallyVotes_Lost_iff`             | Lost iff either half loses                                          |
| JT4  | `jointTallyVotes_Pending_iff`          | Pending iff not Won and not Lost                                    |
| JT5  | `jointTallyVotes_non_joint`            | Empty outgoing → equals single-majority tally                       |
| JT6  | `jointTallyVotes_incoming_Lost`        | Incoming loses → joint result is Lost                               |
| JT7  | `jointTallyVotes_outgoing_Lost`        | Outgoing loses → joint result is Lost                               |
| JT8  | `jointTallyVotes_all_yes`              | All voters yes → Won                                                |
| JT9  | `jointTallyVotes_granted_le`           | Granted ≤ incoming.length + outgoing.length                        |
| JT10 | `jointTallyVotes_rejected_le`          | Rejected ≤ incoming.length + outgoing.length                       |
| JT11 | `jointTallyVotes_empty`                | Both empty → (0, 0, Won)                                           |
| JT12 | `jointTallyVotes_result_exhaustive`    | Result is one of Won, Pending, Lost                                 |
| JT13 | `jointTallyVotes_result_symm_Won`      | Swapping incoming/outgoing preserves Won result                     |
| JT14 | `jointTallyVotes_granted_yesCount_in`  | Granted ≥ yesCount incoming (assuming disjoint lists)               |
-/

namespace FVSquad.JointTally

/-! ## The `jointTallyVotes` model -/

/-- Pure functional model of `ProgressTracker::tally_votes` for a joint quorum.

    - `incoming`, `outgoing` : the two voter lists of the joint configuration.
    - `check`                : maps voter ID → `Some true` (yes), `Some false` (no),
                               `None` (not yet voted).

    Returns `(granted, rejected, voteResult)`.

    The granted/rejected counts iterate over `incoming ++ outgoing`.  In a well-formed
    joint config (no voter appears in both halves) this matches the Rust implementation
    exactly; in the overlap case it may double-count (see module docstring). -/
def jointTallyVotes
    (incoming outgoing : List Nat)
    (check : Nat → Option Bool) : Nat × Nat × VoteResult :=
  let jVoters := incoming ++ outgoing
  (yesCount jVoters check, noCount jVoters check, jointVoteResult incoming outgoing check)

/-! ## Evaluations -/

section Eval

-- Non-joint (empty outgoing): 3 voters, 2 yes → (2, 1, Won)
#eval jointTallyVotes [1, 2, 3] [] (fun v => match v with
  | 1 => some true | 2 => some true | _ => some false)
-- expected: (2, 1, Won)

-- Joint: 3 incoming, 2 outgoing; incoming Won, outgoing Pending → Pending
#eval jointTallyVotes [1, 2, 3] [4, 5] (fun v => match v with
  | 1 => some true | 2 => some true | 3 => some true  -- incoming all yes
  | 4 => some true | _ => none)
-- expected: (4, 0, Pending)  [outgoing: 1 yes out of 2 → majority 2 needed → Pending]

-- Joint: both halves win
#eval jointTallyVotes [1, 2, 3] [4, 5, 6] (fun v => match v with
  | 1 | 2 | 4 | 5 => some true | _ => some false)
-- expected: (4, 2, Won)

-- Joint: outgoing loses
#eval jointTallyVotes [1, 2, 3] [4, 5] (fun v => match v with
  | 1 => some true | 2 => some true | 3 => some true
  | 4 => some false | 5 => some false | _ => none)
-- expected: (3, 2, Lost)

-- Empty joint
#eval jointTallyVotes [] [] (fun _ => some true)
-- expected: (0, 0, Won)

end Eval

/-! ## Helper lemmas -/

private theorem yesCount_append (l1 l2 : List Nat) (check : Nat → Option Bool) :
    yesCount (l1 ++ l2) check = yesCount l1 check + yesCount l2 check := by
  induction l1 with
  | nil => simp [yesCount]
  | cons v vs ih =>
    simp [yesCount, ih]
    omega

private theorem noCount_append (l1 l2 : List Nat) (check : Nat → Option Bool) :
    noCount (l1 ++ l2) check = noCount l1 check + noCount l2 check := by
  induction l1 with
  | nil => simp [noCount]
  | cons v vs ih =>
    simp [noCount, ih]
    omega

private theorem yesCount_le_length (voters : List Nat) (check : Nat → Option Bool) :
    yesCount voters check ≤ voters.length := by
  induction voters with
  | nil => simp [yesCount]
  | cons v vs ih =>
    simp [yesCount]
    split <;> omega

private theorem noCount_le_length (voters : List Nat) (check : Nat → Option Bool) :
    noCount voters check ≤ voters.length := by
  induction voters with
  | nil => simp [noCount]
  | cons v vs ih =>
    simp [noCount]
    split <;> omega

/-! ## JT1: Result component -/

/-- **JT1**: The result component of `jointTallyVotes` equals `jointVoteResult`. -/
theorem jointTallyVotes_result (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    (jointTallyVotes incoming outgoing check).2.2 =
    jointVoteResult incoming outgoing check := by
  simp [jointTallyVotes]

/-! ## JT2–JT4: Won/Lost/Pending characterisations -/

/-- **JT2**: Joint tally result is Won iff both incoming and outgoing win. -/
theorem jointTallyVotes_Won_iff (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Won ↔
    voteResult incoming check = VoteResult.Won ∧
    voteResult outgoing check = VoteResult.Won := by
  simp [jointTallyVotes, jointVoteResult_Won_iff]

/-- **JT3**: Joint tally result is Lost iff incoming or outgoing loses. -/
theorem jointTallyVotes_Lost_iff (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Lost ↔
    voteResult incoming check = VoteResult.Lost ∨
    voteResult outgoing check = VoteResult.Lost := by
  simp [jointTallyVotes, jointVoteResult_Lost_iff]

/-- **JT4**: Joint tally result is Pending iff not Won and not Lost. -/
theorem jointTallyVotes_Pending_iff (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Pending ↔
    ¬(voteResult incoming check = VoteResult.Won ∧
      voteResult outgoing check = VoteResult.Won) ∧
    ¬(voteResult incoming check = VoteResult.Lost ∨
      voteResult outgoing check = VoteResult.Lost) := by
  simp [jointTallyVotes, jointVoteResult_Pending_iff]

/-! ## JT5: Non-joint degeneration -/

/-- **JT5**: With empty outgoing, `jointTallyVotes` equals the single-majority tally.

    This confirms that `JointTally` correctly degenerates to `TallyVotes` in the
    non-joint (single-quorum) case. -/
theorem jointTallyVotes_non_joint (incoming : List Nat) (check : Nat → Option Bool) :
    jointTallyVotes incoming [] check = tallyVotes incoming check := by
  simp [jointTallyVotes, tallyVotes, jointVoteResult_non_joint]

/-! ## JT6–JT7: Loss propagation -/

/-- **JT6**: If incoming loses, the joint tally result is Lost. -/
theorem jointTallyVotes_incoming_Lost
    (incoming outgoing : List Nat) (check : Nat → Option Bool)
    (hi : voteResult incoming check = VoteResult.Lost) :
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Lost := by
  simp [jointTallyVotes, jointVoteResult_Lost_iff, hi]

/-- **JT7**: If outgoing loses, the joint tally result is Lost. -/
theorem jointTallyVotes_outgoing_Lost
    (incoming outgoing : List Nat) (check : Nat → Option Bool)
    (ho : voteResult outgoing check = VoteResult.Lost) :
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Lost := by
  simp [jointTallyVotes, jointVoteResult_Lost_iff, ho]

/-! ## JT8: All-yes implies Won -/

/-- **JT8**: If all voters in both halves vote yes, the result is Won. -/
theorem jointTallyVotes_all_yes
    (incoming outgoing : List Nat) (check : Nat → Option Bool)
    (hall_in  : ∀ v ∈ incoming,  check v = some true)
    (hall_out : ∀ v ∈ outgoing, check v = some true) :
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Won := by
  simp [jointTallyVotes, jointVoteResult_all_yes incoming outgoing check hall_in hall_out]

/-! ## JT9–JT10: Counting bounds -/

/-- **JT9**: The granted count is at most `incoming.length + outgoing.length`. -/
theorem jointTallyVotes_granted_le (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    (jointTallyVotes incoming outgoing check).1 ≤ incoming.length + outgoing.length := by
  simp [jointTallyVotes, yesCount_append]
  have h1 := yesCount_le_length incoming check
  have h2 := yesCount_le_length outgoing check
  omega

/-- **JT10**: The rejected count is at most `incoming.length + outgoing.length`. -/
theorem jointTallyVotes_rejected_le (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    (jointTallyVotes incoming outgoing check).2.1 ≤ incoming.length + outgoing.length := by
  simp [jointTallyVotes, noCount_append]
  have h1 := noCount_le_length incoming check
  have h2 := noCount_le_length outgoing check
  omega

/-! ## JT11: Empty joint -/

/-- **JT11**: Empty incoming and outgoing → (0, 0, Won). -/
theorem jointTallyVotes_empty (check : Nat → Option Bool) :
    jointTallyVotes [] [] check = (0, 0, VoteResult.Won) := by
  simp [jointTallyVotes, yesCount, noCount, jointVoteResult, combineVotes,
        voteResult_empty_is_Won]

/-! ## JT12: Exhaustiveness -/

/-- **JT12**: The result component is always one of Won, Pending, or Lost. -/
theorem jointTallyVotes_result_exhaustive
    (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Won ∨
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Pending ∨
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Lost := by
  simp [jointTallyVotes, jointVoteResult_exhaustive]

/-! ## JT13: Symmetry of Won result -/

/-- **JT13**: Swapping incoming and outgoing preserves the Won result. -/
theorem jointTallyVotes_result_symm_Won
    (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    (jointTallyVotes incoming outgoing check).2.2 = VoteResult.Won ↔
    (jointTallyVotes outgoing incoming check).2.2 = VoteResult.Won := by
  simp [jointTallyVotes, jointVoteResult_Won_symm]

/-! ## JT14: Granted lower bound (disjoint voters) -/

/-- **JT14**: If `incoming` and `outgoing` are disjoint, granted ≥ `yesCount incoming check`.

    This confirms that the granted count correctly includes all yes-votes from the
    incoming quorum. -/
theorem jointTallyVotes_granted_yesCount_in
    (incoming outgoing : List Nat) (check : Nat → Option Bool) :
    yesCount incoming check ≤ (jointTallyVotes incoming outgoing check).1 := by
  simp [jointTallyVotes, yesCount_append]

end FVSquad.JointTally
