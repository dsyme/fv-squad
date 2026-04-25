# Configuration Invariants Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Overview

These tests validate that the Lean `VotersLearnersDisjoint` invariant model in
`formal-verification/lean/FVSquad/ConfigurationInvariants.lean` agrees with
the `Configuration` struct semantics in `src/tracker.rs`.

## Test Strategy (Task 8, Route B)

**Lean side** (`ConfigurationInvariantsCorrespondence.lean`):
- 15 `#guard` assertions evaluated at `lake build` time.
- Tests the computable `votersLearnersDjB` predicate on 12 concrete
  `(incoming_voters, outgoing_voters, learners, learners_next)` tuples.
- Also verifies `allVoters` computation and `mkConfiguration` invariant.

**Rust side** (`src/tracker.rs::test_configuration_invariants_correspondence`):
- 12 cases using inline `voters_learners_disjoint` helper.
- Asserts the same expected Bool on the same concrete tuples.

## How to Run

```bash
# Lean side
cd formal-verification/lean && lake build

# Rust side
cargo test test_configuration_invariants_correspondence --features protobuf-codec
```

## Test Cases (12)

| ID | incoming | outgoing | learners | learners_next | expected | Notes |
|----|----------|----------|----------|---------------|---------|-------|
| 1  | []       | []       | []       | []            | true    | empty config |
| 2  | [1,2,3]  | []       | [4,5]    | []            | true    | simple disjoint |
| 3  | [1,2,3]  | []       | []       | []            | true    | no learners |
| 4  | [1,2]    | [2,3]    | [4]      | []            | true    | joint config, disjoint |
| 5  | [1,2]    | [1,2,3]  | []       | [3]           | false   | demotion: 3 in outgoing+learners_next |
| 6  | [1,2]    | []       | [2,3]    | []            | false   | 2 in incoming+learners |
| 7  | []       | [1,2,3]  | [2]      | []            | false   | 2 in outgoing+learners |
| 8  | [1]      | []       | []       | [1]           | false   | 1 in incoming+learners_next |
| 9  | []       | [5]      | []       | [5]           | false   | 5 in outgoing+learners_next |
| 10 | [1,2,3]  | [4,5,6]  | [7,8]    | []            | true    | fully disjoint joint config |
| 11 | [1]      | [2]      | [3]      | [4]           | true    | all different peers |
| 12 | [1,2,3]  | [1,2,3]  | [1]      | []            | false   | 1 in incoming+outgoing+learners |

## Key Finding

Case 5 reveals that the Lean `VotersLearnersDisjoint` invariant (which requires
`outgoing_voters ∩ learners_next = ∅`) is **stricter** than the Rust intermediate
demotion state allows. In Rust, a peer can be in both `outgoing_voters` and
`learners_next` during joint-config transition. The Lean invariant applies to
fully-finalised configurations, not intermediate joint states. See `RESEARCH.md`
Run 103 update for details.
