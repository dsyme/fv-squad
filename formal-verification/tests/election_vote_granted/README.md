# Election Vote-Granting Correspondence Tests

> 🔬 *Lean Squad — Task 8, Route B.*

## Purpose

Validates that the Lean 4 `voteGranted` and `processVoteRequest` models in
`formal-verification/lean/FVSquad/ElectionCorrespondence.lean` agree with the Rust
vote-granting logic in `src/raft.rs` (lines 1492–1530).

## Scope

- **`voteGranted`** (15 cases): tests the pure Boolean vote-granting condition.
- **`processVoteRequest`** (8 cases): tests the state transition after processing a
  vote request.

## Abstraction level

**Abstraction**: the Lean model omits `leader_id` tracking, priority tie-breaking, and
pre-vote handling. The correspondence holds on the shared inputs (term, votedFor,
log freshness). Both sides compute identical results on all 23 test cases.

## Running the tests

**Lean side** (`#guard` at compile time):
```bash
cd formal-verification/lean
lake build FVSquad.ElectionCorrespondence
# Build succeeds iff all #guard assertions pass
```

**Rust side** (run-time assertions):
```bash
cargo test test_election_vote_granted_correspondence
```

## voteGranted cases (15 total)

| # | voter (term,idx) | priorVote | cand | candLastTerm | candLastIdx | Expected | Reason |
|---|-----------------|-----------|------|-------------|------------|---------|--------|
| 1 | (3,3) | None | 5 | 4 | 3 | true | Fresh vote, cand higher term |
| 2 | (3,3) | Some(5) | 5 | 4 | 3 | true | Repeat vote for same cand |
| 3 | (3,3) | Some(7) | 5 | 4 | 3 | false | Prior vote for different cand |
| 4 | (3,3) | None | 5 | 2 | 3 | false | Cand term lower → not up-to-date |
| 5 | (3,3) | None | 5 | 3 | 3 | true | Equal log → up-to-date |
| 6 | (3,3) | None | 5 | 3 | 2 | false | Same term but shorter cand log |
| 7 | (0,0) | None | 1 | 0 | 0 | true | Empty voter log, empty cand log |
| 8 | (0,0) | Some(1) | 1 | 0 | 0 | true | Empty voter log, repeat vote |
| 9 | (0,0) | Some(2) | 1 | 0 | 0 | false | Empty voter log, wrong prior vote |
| 10 | (5,10) | None | 3 | 6 | 0 | true | Higher cand term wins |
| 11 | (5,10) | None | 3 | 4 | 5 | false | Lower cand term loses |
| 12 | (5,10) | Some(3) | 3 | 6 | 0 | true | Prior vote + higher term |
| 13 | (5,10) | Some(4) | 3 | 6 | 0 | false | Prior vote for different cand |
| 14 | (1,1) | None | 2 | 1 | 1 | true | Equal log, fresh vote |
| 15 | (1,1) | None | 2 | 1 | 0 | false | Same term, shorter cand log |

## processVoteRequest cases (8 total)

| # | s.term | s.votedFor | voterLog | cand | cTerm | cLT | cLI | Result.term | Result.votedFor |
|---|--------|-----------|----------|------|-------|-----|-----|------------|----------------|
| 1 | 1 | None | (3,3) | 5 | 1 | 4 | 3 | 1 | Some(5) |
| 2 | 1 | Some(5) | (3,3) | 5 | 1 | 4 | 3 | 1 | Some(5) |
| 3 | 1 | Some(7) | (3,3) | 5 | 1 | 4 | 3 | 1 | Some(7) |
| 4 | 1 | None | (3,3) | 5 | 2 | 4 | 3 | 2 | Some(5) |
| 5 | 1 | None | (3,3) | 5 | 2 | 2 | 1 | 2 | None |
| 6 | 1 | None | (3,3) | 5 | 1 | 3 | 2 | 1 | None |
| 7 | 2 | Some(3) | (1,1) | 5 | 3 | 2 | 0 | 3 | Some(5) |
| 8 | 2 | Some(3) | (4,5) | 5 | 3 | 2 | 0 | 3 | None |

## Last run

Run 100 — 2026-04-24. All 23 cases pass on both sides. Lean: `lake build` ✅. Rust: `cargo test` ✅.
