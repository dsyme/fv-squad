import FVSquad.HasQuorum

/-!
# HasQuorum Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `has_quorum`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/has_quorum/cases.json` are
mirrored both here (Lean model side) and in
`src/tracker.rs::test_has_quorum_correspondence`
(Rust source side).  Both sides must produce the same `expected` Boolean value on the same
`(voters, set_ids)` input.

- **Lean side**: `#guard` evaluates `hasQuorum voters (inSetFn set_ids) == expected`
  at lake-build time.  A compile error means the Lean model gives a different answer.
- **Rust side**: `assert_eq!` in the test function verifies the same expected values at
  `cargo test` time.

Together they demonstrate that the Lean model and the Rust `ProgressTracker::has_quorum`
agree on all 12 correspondence cases.

## What is checked

For each case we check one observable property:

- **Return value**: `hasQuorum voters (inSetFn set_ids) == expected`

where `inSetFn set_ids v = set_ids.contains v` (membership predicate).

The Lean model abstracts `HashSet<u64>` as a `Nat → Bool` predicate, and
`ProgressTracker::conf.voters` as a `List Nat`.  The abstraction is exact
for the `use_group_commit = false` path (which is the default and the only path
modelled in `HasQuorum.lean`).

## Test cases (12 total)

| ID | voters | set_ids | expected | Notes |
|----|--------|---------|---------|-------|
| 1  | [] | [] | true | Empty voters → always true |
| 2  | [1] | [1] | true | Singleton quorum met |
| 3  | [1] | [] | false | Singleton quorum not met |
| 4  | [1,2,3] | [1,2] | true | 2 ≥ majority(3)=2 |
| 5  | [1,2,3] | [1] | false | 1 < majority(3)=2 |
| 6  | [1,2,3] | [1,2,3] | true | All voters present |
| 7  | [1,2,3] | [] | false | No voters present |
| 8  | [1,2,3,4,5] | [1,2,3] | true | 3=majority(5) |
| 9  | [1,2,3,4,5] | [1,2] | false | 2 < majority(5)=3 |
| 10 | [1,2,3,4,5] | [1,2,3,4] | true | 4 ≥ 3 |
| 11 | [1,2,3,4,5] | [1,2,4,5] | true | Non-consecutive IDs, 4 ≥ 3 |
| 12 | [1,2,3,4,5] | [5] | false | Only 1 voter present, 1 < 3 |
-/

namespace FVSquad.HasQuorumCorrespondence

/-! ## Helper: build a membership predicate from an ID list -/

/-- Build an `inSet` predicate from a list of IDs that are present in the set.
    Mirrors `potential_quorum.get(&id).map(|_| true)` in `has_quorum`. -/
private def inSetFn (set_ids : List Nat) : Nat → Bool :=
  fun v => set_ids.contains v

/-! ## Sanity checks for `inSetFn` -/

#guard inSetFn [1,2,3] 1 == true
#guard inSetFn [1,2,3] 4 == false
#guard inSetFn [] 1 == false

/-! ## Case 1: Empty voters → true (always) -/

#guard hasQuorum [] (inSetFn []) == true

/-! ## Case 2: Single voter in set → true
    overlap=1 ≥ majority(1)=1 -/

#guard hasQuorum [1] (inSetFn [1]) == true

/-! ## Case 3: Single voter not in set → false
    overlap=0 < majority(1)=1 -/

#guard hasQuorum [1] (inSetFn []) == false

/-! ## Case 4: 3 voters, 2 in set → true
    overlap=2 ≥ majority(3)=2 -/

#guard hasQuorum [1,2,3] (inSetFn [1,2]) == true

/-! ## Case 5: 3 voters, 1 in set → false
    overlap=1 < majority(3)=2 -/

#guard hasQuorum [1,2,3] (inSetFn [1]) == false

/-! ## Case 6: 3 voters, all in set → true
    overlap=3 ≥ majority(3)=2 -/

#guard hasQuorum [1,2,3] (inSetFn [1,2,3]) == true

/-! ## Case 7: 3 voters, none in set → false
    overlap=0 < majority(3)=2 -/

#guard hasQuorum [1,2,3] (inSetFn []) == false

/-! ## Case 8: 5 voters, 3 in set → true (exactly at threshold)
    overlap=3 = majority(5)=3 -/

#guard hasQuorum [1,2,3,4,5] (inSetFn [1,2,3]) == true

/-! ## Case 9: 5 voters, 2 in set → false
    overlap=2 < majority(5)=3 -/

#guard hasQuorum [1,2,3,4,5] (inSetFn [1,2]) == false

/-! ## Case 10: 5 voters, 4 in set → true
    overlap=4 ≥ majority(5)=3 -/

#guard hasQuorum [1,2,3,4,5] (inSetFn [1,2,3,4]) == true

/-! ## Case 11: 5 voters, 4 in set (non-consecutive IDs) → true
    Voters 1,2,4,5 present; voter 3 absent.  overlap=4 ≥ 3 -/

#guard hasQuorum [1,2,3,4,5] (inSetFn [1,2,4,5]) == true

/-! ## Case 12: 5 voters, only 1 in set → false
    overlap=1 < majority(5)=3 -/

#guard hasQuorum [1,2,3,4,5] (inSetFn [5]) == false

end FVSquad.HasQuorumCorrespondence
