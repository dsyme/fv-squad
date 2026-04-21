# tally_votes Correspondence Tests

> 🔬 *Lean Squad — Task 8 Route B correspondence tests.*

## What is validated

`ProgressTracker::tally_votes` from `src/tracker.rs`. The Lean model `tallyVotes`
in `FVSquad/TallyVotes.lean` maps `(voters, check)` to `(granted, rejected, VoteResult)`.

## Abstraction

| Lean | Rust |
|------|------|
| `voters : List Nat` | `tracker.conf.voters` (JointConfig majority path) |
| `check : Nat → Option Bool` | `tracker.votes.get(&id).cloned()` |
| `some true` | voted yes |
| `some false` | voted no |
| `none` | not yet voted |
| `VoteResult.Won` | `VoteResult::Won` |
| `VoteResult.Lost` | `VoteResult::Ineligible` (mapped to Lost) |
| `VoteResult.Pending` | `VoteResult::Pending` |

Note: The Lean `VoteResult.Lost` corresponds to Rust `VoteResult::Ineligible`
(used when majority of no-votes makes winning impossible).

## Test commands

**Lean (static, at build time):**
```bash
cd formal-verification/lean
lake build FVSquad.TallyVotesCorrespondence
```

**Rust (runtime):**
```bash
cargo test test_tally_votes_correspondence
```

## Cases (10 total)

| ID | voters | yes | no | granted | rejected | result |
|----|--------|-----|----|---------|----------|--------|
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

## Result

Both sides agree on all 10 cases. Correspondence level: **Exact** for the
majority-quorum path (single-voter-set, `use_group_commit=false`).
