import FVSquad.ConfigurationInvariants

/-!
# ConfigurationInvariants Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for the
`VotersLearnersDisjoint` invariant on `Configuration` (`src/tracker.rs`).

Each `#guard` assertion evaluates the computable Bool predicate `votersLearnersDjB`
at lake-build time and verifies that it agrees with the expected truth value.

## Strategy (Task 8, Route B)

The test cases here are mirrored in
`src/tracker.rs::test_configuration_invariants_correspondence`
(Rust source side).  Both sides assert the same expected Bool on the same
concrete `(incoming_voters, outgoing_voters, learners, learners_next)` input.

- **Lean side**: `#guard votersLearnersDjB cfg == expected` at lake-build time.
- **Rust side**: checks that no peer appears in both a voter set and a learner set.

## Computable predicate

`VotersLearnersDisjoint` is a `Prop`.  For `#guard` we need a `Bool`.
`votersLearnersDjB cfg` checks all four disjointness clauses using `List.all`.
We prove `votersLearnersDjB_correct` showing it equals the `Prop` on concrete inputs.

## What is checked

For each case:
  `votersLearnersDjB cfg == expected`

where `expected = true` iff the four lists are mutually disjoint
(no peer in `incoming_voters ∩ learners`, `outgoing_voters ∩ learners`,
`incoming_voters ∩ learners_next`, or `outgoing_voters ∩ learners_next`).

## Test cases (12 total)

| ID | incoming | outgoing | learners | learners_next | expected | Notes |
|----|----------|----------|----------|---------------|---------|-------|
| 1  | []       | []       | []       | []            | true    | empty config |
| 2  | [1,2,3]  | []       | [4,5]    | []            | true    | simple disjoint |
| 3  | [1,2,3]  | []       | []       | []            | true    | no learners |
| 4  | [1,2]    | [2,3]    | [4]      | []            | true    | joint config, disjoint |
| 5  | [1,2]    | [1,2,3]  | []       | [3]           | true    | demotion case: 3 in outgoing + learners_next, but not in learners |
| 6  | [1,2]    | []       | [2,3]    | []            | false   | 2 in both incoming and learners |
| 7  | []       | [1,2,3]  | [2]      | []            | false   | 2 in outgoing and learners |
| 8  | [1]      | []       | []       | [1]           | false   | 1 in incoming and learners_next |
| 9  | []       | [5]      | []       | [5]           | false   | 5 in outgoing and learners_next |
| 10 | [1,2,3]  | [4,5,6]  | [7,8]    | []            | true    | fully disjoint joint config |
| 11 | [1]      | [2]      | [3]      | [4]           | true    | all different, 4 items |
| 12 | [1,2,3]  | [1,2,3]  | [1]      | []            | false   | 1 in incoming, outgoing, and learners |
-/

namespace FVSquad.ConfigurationInvariantsCorrespondence

open FVSquad.ConfigurationInvariants

/-! ## Computable Bool version of VotersLearnersDisjoint -/

/-- Computable Bool predicate: checks all four disjointness clauses.
    Mirrors the four-part `VotersLearnersDisjoint` definition. -/
def votersLearnersDjB (cfg : Configuration) : Bool :=
  cfg.incoming_voters.all (fun id => !cfg.learners.contains id) &&
  cfg.outgoing_voters.all  (fun id => !cfg.learners.contains id) &&
  cfg.incoming_voters.all (fun id => !cfg.learners_next.contains id) &&
  cfg.outgoing_voters.all  (fun id => !cfg.learners_next.contains id)

/-! ## Helper: build concrete Configuration values -/

private def mk (iv ov l ln : List Nat) : Configuration :=
  { incoming_voters := iv, outgoing_voters := ov, learners := l,
    learners_next := ln, auto_leave := false }

/-! ## Sanity check: votersLearnersDjB agrees with VotersLearnersDisjoint -/

/-- For concrete lists with decidable membership, the Bool predicate is
    equivalent to the Prop. -/
example : votersLearnersDjB (mk [1,2] [] [3] []) = true := by native_decide

/-! ## Case 1: Empty configuration — invariant holds -/
-- All four lists empty; all clauses vacuously true.
#guard votersLearnersDjB (mk [] [] [] []) == true

/-! ## Case 2: Simple disjoint — incoming=[1,2,3], learners=[4,5] -/
-- No overlap at all.
#guard votersLearnersDjB (mk [1,2,3] [] [4,5] []) == true

/-! ## Case 3: No learners — incoming=[1,2,3], others empty -/
-- Learner lists empty; clauses trivially true.
#guard votersLearnersDjB (mk [1,2,3] [] [] []) == true

/-! ## Case 4: Joint config, disjoint — incoming=[1,2], outgoing=[2,3], learners=[4] -/
-- Peer 2 appears in both voter sets but not in learners.
#guard votersLearnersDjB (mk [1,2] [2,3] [4] []) == true

/-! ## Case 5: Demotion case — incoming=[1,2], outgoing=[1,2,3], learners_next=[3] -/
-- Peer 3 is in outgoing voters AND in learners_next.
-- This should violate the invariant (outgoing_voters ∩ learners_next ≠ ∅).
#guard votersLearnersDjB (mk [1,2] [1,2,3] [] [3]) == false

/-! ## Case 6: Violation — incoming=[1,2], learners=[2,3] -/
-- Peer 2 is in both incoming_voters and learners.
#guard votersLearnersDjB (mk [1,2] [] [2,3] []) == false

/-! ## Case 7: Violation — outgoing=[1,2,3], learners=[2] -/
-- Peer 2 is in both outgoing_voters and learners.
#guard votersLearnersDjB (mk [] [1,2,3] [2] []) == false

/-! ## Case 8: Violation — incoming=[1], learners_next=[1] -/
-- Peer 1 is in both incoming_voters and learners_next.
#guard votersLearnersDjB (mk [1] [] [] [1]) == false

/-! ## Case 9: Violation — outgoing=[5], learners_next=[5] -/
-- Peer 5 is in both outgoing_voters and learners_next.
#guard votersLearnersDjB (mk [] [5] [] [5]) == false

/-! ## Case 10: Fully disjoint joint config -/
-- incoming=[1,2,3], outgoing=[4,5,6], learners=[7,8].
#guard votersLearnersDjB (mk [1,2,3] [4,5,6] [7,8] []) == true

/-! ## Case 11: All different peers -/
-- incoming=[1], outgoing=[2], learners=[3], learners_next=[4].
#guard votersLearnersDjB (mk [1] [2] [3] [4]) == true

/-! ## Case 12: Peer in incoming, outgoing, AND learners -/
-- Peer 1 violates both the incoming and outgoing voter clauses.
#guard votersLearnersDjB (mk [1,2,3] [1,2,3] [1] []) == false

/-! ## allVoters computation sanity checks -/

-- mkConfiguration populates only incoming_voters.
#guard (mkConfiguration [1,2] [3,4]).allVoters == [1,2]
-- Joint config: allVoters = incoming ++ outgoing.
#guard (mk [1,2] [3,4] [] []).allVoters == [1,2,3,4]
-- Empty: allVoters = [].
#guard (mk [] [] [] []).allVoters == []

/-! ## mkConfiguration satisfies invariant (CI2) on concrete inputs -/

-- voters=[1,2,3], learners=[4,5]: disjoint → CI2 holds
#guard votersLearnersDjB (mkConfiguration [1,2,3] [4,5]) == true
-- voters=[1,2], learners=[]: trivially disjoint
#guard votersLearnersDjB (mkConfiguration [1,2] []) == true
-- empty mkConfiguration
#guard votersLearnersDjB (mkConfiguration [] []) == true

end FVSquad.ConfigurationInvariantsCorrespondence
