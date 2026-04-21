import FVSquad.TallyVotes

/-!
# TallyVotes Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `tally_votes`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/tally_votes/cases.json` are
mirrored both here (Lean model side) and in
`src/tracker.rs::test_tally_votes_correspondence`
(Rust source side).  Both sides must produce the same `(granted, rejected, result)`
triple on the same `(voters, yes_ids, no_ids)` input.

- **Lean side**: `#guard` evaluates `tallyVotes voters (checkFn yes_ids no_ids)`
  at lake-build time.
- **Rust side**: `assert_eq!` in the test verifies the same triple at `cargo test` time.

## Abstraction

The Lean model maps `(voters, check)` to `(granted, rejected, VoteResult)` where:
- `check voter = some true`  → yes-vote
- `check voter = some false` → no-vote
- `check voter = none`       → missing (not yet voted)

The Rust `ProgressTracker::tally_votes` counts votes among `conf.voters`.
The `checkFn yes_ids no_ids` helper builds the check function from two ID lists.

## Test cases (10 total)

| ID | voters | yes_ids | no_ids | granted | rejected | result |
|----|--------|---------|--------|---------|----------|--------|
| 1  | [] | [] | [] | 0 | 0 | Won |
| 2  | [1] | [1] | [] | 1 | 0 | Won |
| 3  | [1] | [] | [1] | 0 | 1 | Lost |
| 4  | [1] | [] | [] | 0 | 0 | Pending |
| 5  | [1,2,3] | [1,2] | [3] | 2 | 1 | Won |
| 6  | [1,2,3] | [1] | [2] | 1 | 1 | Pending |
| 7  | [1,2,3] | [] | [1,2] | 0 | 2 | Lost |
| 8  | [1,2,3] | [1,2,3] | [] | 3 | 0 | Won |
| 9  | [1,2,3,4,5] | [1,2,3] | [4,5] | 3 | 2 | Won |
| 10 | [1,2,3,4,5] | [1] | [2,3,4,5] | 1 | 4 | Lost |
-/

namespace FVSquad.TallyVotesCorrespondence

/-! ## Helper: build check function from yes/no ID lists -/

/-- Build a check function: yes_ids → Some true, no_ids → Some false, else None. -/
private def checkFn (yes_ids no_ids : List Nat) : Nat → Option Bool :=
  fun v =>
    if yes_ids.contains v then some true
    else if no_ids.contains v then some false
    else none

/-! ## Case 1: Empty voters → (0, 0, Won) -/

#guard tallyVotes [] (checkFn [] []) == (0, 0, VoteResult.Won)

/-! ## Case 2: Single voter yes → (1, 0, Won) -/

#guard tallyVotes [1] (checkFn [1] []) == (1, 0, VoteResult.Won)

/-! ## Case 3: Single voter no → (0, 1, Lost) -/

#guard tallyVotes [1] (checkFn [] [1]) == (0, 1, VoteResult.Lost)

/-! ## Case 4: Single voter missing → (0, 0, Pending) -/

#guard tallyVotes [1] (checkFn [] []) == (0, 0, VoteResult.Pending)

/-! ## Case 5: 3 voters: 2 yes, 1 no → (2, 1, Won) — majority met -/

#guard tallyVotes [1, 2, 3] (checkFn [1, 2] [3]) == (2, 1, VoteResult.Won)

/-! ## Case 6: 3 voters: 1 yes, 1 no, 1 missing → (1, 1, Pending)
    1 yes + 1 missing (could win) but not certain → Pending -/

#guard tallyVotes [1, 2, 3] (checkFn [1] [2]) == (1, 1, VoteResult.Pending)

/-! ## Case 7: 3 voters: 0 yes, 2 no, 1 missing → (0, 2, Lost)
    Rejections exceed majority threshold → Lost -/

#guard tallyVotes [1, 2, 3] (checkFn [] [1, 2]) == (0, 2, VoteResult.Lost)

/-! ## Case 8: 3 voters, all yes → (3, 0, Won) -/

#guard tallyVotes [1, 2, 3] (checkFn [1, 2, 3] []) == (3, 0, VoteResult.Won)

/-! ## Case 9: 5 voters: 3 yes, 2 no → (3, 2, Won) -/

#guard tallyVotes [1, 2, 3, 4, 5] (checkFn [1, 2, 3] [4, 5]) == (3, 2, VoteResult.Won)

/-! ## Case 10: 5 voters: 1 yes, 4 no → (1, 4, Lost) -/

#guard tallyVotes [1, 2, 3, 4, 5] (checkFn [1] [2, 3, 4, 5]) == (1, 4, VoteResult.Lost)

end FVSquad.TallyVotesCorrespondence
