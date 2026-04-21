import FVSquad.MajorityVote

/-!
# VoteResult Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `vote_result`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/vote_result/cases.json` are
mirrored both here (Lean model side) and in
`src/quorum/majority.rs::test_vote_result_correspondence`
(Rust source side).  Both sides must produce the same `expected` VoteResult on the same
`(voters, yes_ids, no_ids)` input.

- **Lean side**: `#guard` evaluates `voteResult voters (checkFn yes_ids no_ids) == expected`
  at lake-build time.  A compile error means the Lean model gives a different answer.
- **Rust side**: `assert_eq!` in the test function verifies the same expected values at
  `cargo test` time.

Together they demonstrate that the Lean model and the Rust `Configuration::vote_result`
agree on all 12 correspondence cases.

## What is checked

For each case we check one observable property:

- **Return value**: `voteResult voters (checkFn yes_ids no_ids) == expected`

The function maps `(voters, yes_ids, no_ids)` to `VoteResult`, where:
- voter ∈ yes_ids → `Some true`
- voter ∈ no_ids → `Some false`
- voter ∉ yes_ids ∪ no_ids → `None` (missing / not yet voted)

## Test cases (12 total)

| ID | voters | yes_ids | no_ids | expected | Notes |
|----|--------|---------|--------|---------|-------|
| 1  | [] | [] | [] | Won | Empty voters convention |
| 2  | [1] | [1] | [] | Won | Single yes → Won |
| 3  | [1] | [] | [1] | Lost | Single no → Lost |
| 4  | [1] | [] | [] | Pending | Single missing → Pending |
| 5  | [1,2,3] | [1,2] | [3] | Won | 2 yes ≥ majority(3)=2 |
| 6  | [1,2,3] | [1] | [2] | Pending | 1 yes + 1 missing ≥ 2 |
| 7  | [1,2,3] | [] | [1,2] | Lost | 0+1 < 2 |
| 8  | [1,2,3] | [1,2,3] | [] | Won | All yes |
| 9  | [1,2,3] | [] | [1,2,3] | Lost | All no |
| 10 | [1,2,3,4,5] | [1,2,3] | [4,5] | Won | 3=majority(5) |
| 11 | [1,2,3,4,5] | [1,2] | [4,5] | Pending | 2+1=3 ≥ 3, but 2 < 3 |
| 12 | [1,2,3,4,5] | [1,2] | [3,4,5] | Lost | 2+0=2 < 3 |
-/

namespace FVSquad.VoteResultCorrespondence

/-! ## Helper: build a check function from yes/no ID lists -/

/-- Build a check function from lists of yes-voter and no-voter IDs.
    Voters not in either list return `none` (not yet voted / missing).
    Mirrors the `yes_ids.contains(&id)` / `no_ids.contains(&id)` logic in the Rust test. -/
private def checkFn (yes_ids no_ids : List Nat) : Nat → Option Bool :=
  fun v =>
    if yes_ids.contains v then some true
    else if no_ids.contains v then some false
    else none

/-! ## Sanity checks for `checkFn` -/

#guard checkFn [1,2] [3] 1 == some true
#guard checkFn [1,2] [3] 3 == some false
#guard checkFn [1,2] [3] 4 == none

/-! ## Case 1: Empty voters → Won (joint-quorum convention) -/

#guard voteResult [] (checkFn [] []) == VoteResult.Won

/-! ## Case 2: Single voter, voted yes → Won -/

#guard voteResult [1] (checkFn [1] []) == VoteResult.Won

/-! ## Case 3: Single voter, voted no → Lost -/

#guard voteResult [1] (checkFn [] [1]) == VoteResult.Lost

/-! ## Case 4: Single voter, missing → Pending
    yes=0 < majority(1)=1; yes+missing=0+1=1 ≥ 1 → Pending -/

#guard voteResult [1] (checkFn [] []) == VoteResult.Pending

/-! ## Case 5: 3 voters, 2 yes, 1 no → Won
    yes=2 ≥ majority(3)=2 → Won -/

#guard voteResult [1,2,3] (checkFn [1,2] [3]) == VoteResult.Won

/-! ## Case 6: 3 voters, 1 yes, 1 no, 1 missing → Pending
    yes=1 < 2; yes+missing=1+1=2 ≥ 2 → Pending -/

#guard voteResult [1,2,3] (checkFn [1] [2]) == VoteResult.Pending

/-! ## Case 7: 3 voters, 0 yes, 1 missing, 2 no → Lost
    yes=0, missing=1 (voter 3); yes+missing=1 < majority(3)=2 → Lost -/

#guard voteResult [1,2,3] (checkFn [] [1,2]) == VoteResult.Lost

/-! ## Case 8: 3 voters, all yes → Won -/

#guard voteResult [1,2,3] (checkFn [1,2,3] []) == VoteResult.Won

/-! ## Case 9: 3 voters, all no → Lost -/

#guard voteResult [1,2,3] (checkFn [] [1,2,3]) == VoteResult.Lost

/-! ## Case 10: 5 voters, 3 yes → Won (exactly at majority threshold)
    yes=3 = majority(5)=3 → Won -/

#guard voteResult [1,2,3,4,5] (checkFn [1,2,3] [4,5]) == VoteResult.Won

/-! ## Case 11: 5 voters, 2 yes, 1 missing, 2 no → Pending
    yes=2 < 3; yes+missing=2+1=3 ≥ 3 → Pending -/

#guard voteResult [1,2,3,4,5] (checkFn [1,2] [4,5]) == VoteResult.Pending

/-! ## Case 12: 5 voters, 2 yes, 3 no → Lost
    yes=2 < 3; yes+missing=2+0=2 < 3 → Lost -/

#guard voteResult [1,2,3,4,5] (checkFn [1,2] [3,4,5]) == VoteResult.Lost

end FVSquad.VoteResultCorrespondence
