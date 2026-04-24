import FVSquad.RaftElection

/-!
# ElectionCorrespondence — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for the Lean election model
against the Rust vote-granting logic in `src/raft.rs`.

## Strategy (Task 8, Route B)

### What we're testing

The Lean `voteGranted` function models the Rust vote-granting condition (§5.2 / §5.4.1):

```lean
def voteGranted (voterLog : LogId) (priorVote : Option Nat)
    (candId candLastTerm candLastIndex : Nat) : Bool :=
  (priorVote = none || priorVote = some candId) &&
  isUpToDate voterLog candLastTerm candLastIndex
```

The Rust equivalent (abstracting away `leader_id` and priority tie-breaking):
```rust
fn vote_granted_model(voter_term, voter_index, prior_vote: Option<u64>,
                      cand_id, cand_last_term, cand_last_index) -> bool {
    let can_vote = match prior_vote {
        None => true,
        Some(c) => c == cand_id,
    };
    let is_up_to_date = cand_last_term > voter_term
        || (cand_last_term == voter_term && cand_last_index >= voter_index);
    can_vote && is_up_to_date
}
```

We also test `processVoteRequest` — the Lean model of the `MsgRequestVote` handler
(Rust `src/raft.rs:1492–1530`).

## Abstraction level

- **`voteGranted`**: **exact** — the Lean model and the Rust model agree on all inputs
  when abstracting away `leader_id` check and priority tie-breaking.
- **`processVoteRequest`**: **abstraction** — the Lean model abstracts away `leader_id`,
  message queues, `election_elapsed`, and priority.  On the shared inputs (term, votedFor,
  log freshness) the outputs agree.

## Rust test

The matching Rust test `test_election_vote_granted_correspondence` in `src/raft.rs`
exercises the same 15 `voteGranted` cases and 8 `processVoteRequest` cases below.

## Test cases

### voteGranted — 15 cases

| # | voterTerm | voterIdx | priorVote | candId | cLastTerm | cLastIdx | Expected | Reason |
|---|-----------|----------|-----------|--------|-----------|----------|---------|--------|
| 1 | 3 | 3 | none | 5 | 4 | 3 | true | Fresh vote, cand higher term |
| 2 | 3 | 3 | some 5 | 5 | 4 | 3 | true | Repeat vote for same cand |
| 3 | 3 | 3 | some 7 | 5 | 4 | 3 | false | Already voted for different cand |
| 4 | 3 | 3 | none | 5 | 2 | 3 | false | Cand term lower → not up-to-date |
| 5 | 3 | 3 | none | 5 | 3 | 3 | true | Equal log → up-to-date |
| 6 | 3 | 3 | none | 5 | 3 | 2 | false | Same term but shorter cand log |
| 7 | 0 | 0 | none | 1 | 0 | 0 | true | Empty voter log, cand log also empty |
| 8 | 0 | 0 | some 1 | 1 | 0 | 0 | true | Empty voter log, repeat vote |
| 9 | 0 | 0 | some 2 | 1 | 0 | 0 | false | Empty voter log, prior vote for different cand |
| 10 | 5 | 10 | none | 3 | 6 | 0 | true | Higher cand term wins |
| 11 | 5 | 10 | none | 3 | 4 | 5 | false | Lower cand term loses |
| 12 | 5 | 10 | some 3 | 3 | 6 | 0 | true | Prior vote + higher term |
| 13 | 5 | 10 | some 4 | 3 | 6 | 0 | false | Prior vote for different cand |
| 14 | 1 | 1 | none | 2 | 1 | 1 | true | Equal log, fresh vote |
| 15 | 1 | 1 | none | 2 | 1 | 0 | false | Same term, shorter cand log |

### processVoteRequest — 8 cases

| # | s.term | s.vote | voterLog | cand | cTerm | cLT | cLI | Expected state |
|---|--------|--------|----------|------|-------|-----|-----|----------------|
| 1 | 1 | none | (3,3) | 5 | 1 | 4 | 3 | t=1, v=some 5, r=Follower |
| 2 | 1 | some 5 | (3,3) | 5 | 1 | 4 | 3 | t=1, v=some 5, r=Follower (idempotent) |
| 3 | 1 | some 7 | (3,3) | 5 | 1 | 4 | 3 | t=1, v=some 7, r=Follower (denied) |
| 4 | 1 | none | (3,3) | 5 | 2 | 4 | 3 | t=2, v=some 5, r=Follower (higher term, granted) |
| 5 | 1 | none | (3,3) | 5 | 2 | 2 | 1 | t=2, v=none, r=Follower (higher term, denied - log stale) |
| 6 | 1 | none | (3,3) | 5 | 1 | 3 | 2 | t=1, v=none, r=Follower (same term, denied - shorter log) |
| 7 | 2 | some 3 | (1,1) | 5 | 3 | 2 | 0 | t=3, v=some 5, r=Follower (higher term, granted - voter log stale) |
| 8 | 2 | some 3 | (4,5) | 5 | 3 | 2 | 0 | t=3, v=none, r=Follower (higher term, denied - voter log fresh) |
-/

namespace FVSquad.ElectionCorrespondence

open FVSquad.RaftElection

/-! ## Voter log fixtures -/

private def voter33  : LogId := { term := 3, index := 3 }
private def voter00  : LogId := { term := 0, index := 0 }
private def voter510 : LogId := { term := 5, index := 10 }
private def voter11  : LogId := { term := 1, index := 1 }
private def voter11' : LogId := { term := 1, index := 1 }
private def voter45  : LogId := { term := 4, index := 5 }

/-! ## NodeState fixtures -/

private def s1  : NodeState := { currentTerm := 1, votedFor := none, role := NodeRole.Follower }
private def s1v5 : NodeState := { currentTerm := 1, votedFor := some 5, role := NodeRole.Follower }
private def s1v7 : NodeState := { currentTerm := 1, votedFor := some 7, role := NodeRole.Follower }
private def s2v3 : NodeState := { currentTerm := 2, votedFor := some 3, role := NodeRole.Follower }

/-! ## voteGranted cases 1–15 -/

-- Case 1: fresh voter (priorVote=none), cand has higher term → true
#guard voteGranted voter33 none 5 4 3 == true

-- Case 2: repeat vote for same candidate → true
#guard voteGranted voter33 (some 5) 5 4 3 == true

-- Case 3: already voted for different candidate → false
#guard voteGranted voter33 (some 7) 5 4 3 == false

-- Case 4: no prior vote, cand term is lower (2 < 3) → not up-to-date → false
#guard voteGranted voter33 none 5 2 3 == false

-- Case 5: same log (both term=3, index=3) → up-to-date (equal) → true
#guard voteGranted voter33 none 5 3 3 == true

-- Case 6: same term but cand index shorter (2 < 3) → false
#guard voteGranted voter33 none 5 3 2 == false

-- Case 7: empty voter log (0,0), cand log also (0,0) → up-to-date → true
#guard voteGranted voter00 none 1 0 0 == true

-- Case 8: empty voter log, repeat vote for same cand → true
#guard voteGranted voter00 (some 1) 1 0 0 == true

-- Case 9: empty voter log, prior vote for different cand → false
#guard voteGranted voter00 (some 2) 1 0 0 == false

-- Case 10: voter log (5,10), cand term=6 > 5 → higher term wins → true
#guard voteGranted voter510 none 3 6 0 == true

-- Case 11: voter log (5,10), cand term=4 < 5 → lower term loses → false
#guard voteGranted voter510 none 3 4 5 == false

-- Case 12: voter log (5,10), prior vote for same cand, higher term → true
#guard voteGranted voter510 (some 3) 3 6 0 == true

-- Case 13: voter log (5,10), prior vote for different cand (4 ≠ 3), even with higher cand term → false
#guard voteGranted voter510 (some 4) 3 6 0 == false

-- Case 14: voter log (1,1), cand log (1,1), fresh vote → equal → up-to-date → true
#guard voteGranted voter11 none 2 1 1 == true

-- Case 15: voter log (1,1), cand log (1,0), same term but shorter cand log → false
#guard voteGranted voter11 none 2 1 0 == false

/-! ## processVoteRequest cases 1–8 -/

-- Case 1: fresh voter, same term, up-to-date cand → vote granted
-- s = {t=1, v=none, r=Follower}, voterLog=(3,3), cand=5, cTerm=1, cLT=4, cLI=3
-- candTerm=1 ≤ currentTerm=1 → same term; voteGranted(none, 5, 4, 3) = true → {s with votedFor=some 5}
#guard
  processVoteRequest s1 voter33 5 1 4 3 ==
  { currentTerm := 1, votedFor := some 5, role := NodeRole.Follower }

-- Case 2: idempotent — already voted for same candidate
-- s = {t=1, v=some 5, r=Follower}, same params → same output
#guard
  processVoteRequest s1v5 voter33 5 1 4 3 ==
  { currentTerm := 1, votedFor := some 5, role := NodeRole.Follower }

-- Case 3: denied — already voted for different candidate (7 ≠ 5)
-- voteGranted(some 7, 5, 4, 3) = false → return s unchanged
#guard
  processVoteRequest s1v7 voter33 5 1 4 3 ==
  { currentTerm := 1, votedFor := some 7, role := NodeRole.Follower }

-- Case 4: higher term (2 > 1), voteGranted(none, 5, 4, 3) w/ voterLog=(3,3):
-- isUpToDate {3,3} 4 3 = true → granted → {t=2, v=some 5, r=Follower}
#guard
  processVoteRequest s1 voter33 5 2 4 3 ==
  { currentTerm := 2, votedFor := some 5, role := NodeRole.Follower }

-- Case 5: higher term (2 > 1), cand log (2,1) vs voter log (3,3):
-- isUpToDate {3,3} 2 1 = false (2 < 3) → not granted → becomeFollower s 2 = {t=2, v=none, r=Follower}
#guard
  processVoteRequest s1 voter33 5 2 2 1 ==
  { currentTerm := 2, votedFor := none, role := NodeRole.Follower }

-- Case 6: same term (1 ≤ 1), cand log (3,2) vs voter log (3,3):
-- isUpToDate {3,3} 3 2 = false (same term, 2 < 3) → not granted → return s unchanged
#guard
  processVoteRequest s1 voter33 5 1 3 2 ==
  { currentTerm := 1, votedFor := none, role := NodeRole.Follower }

-- Case 7: higher term (3 > 2), voter log (1,1), cand log (2,0):
-- isUpToDate {1,1} 2 0 = true (2 > 1) → granted → {t=3, v=some 5, r=Follower}
#guard
  processVoteRequest s2v3 voter11 5 3 2 0 ==
  { currentTerm := 3, votedFor := some 5, role := NodeRole.Follower }

-- Case 8: higher term (3 > 2), voter log (4,5), cand log (2,0):
-- isUpToDate {4,5} 2 0 = false (2 < 4) → not granted → becomeFollower s 3 = {t=3, v=none, r=Follower}
#guard
  processVoteRequest s2v3 voter45 5 3 2 0 ==
  { currentTerm := 3, votedFor := none, role := NodeRole.Follower }

/-! ## Cross-checks: voteGranted ↔ processVoteRequest consistency -/

-- When voteGranted returns true for same-term request, processVoteRequest gives votedFor = some candId
#guard (voteGranted voter33 none 5 4 3 == true) &&
       (processVoteRequest s1 voter33 5 1 4 3).votedFor == some 5

-- When voteGranted returns false for same-term request, processVoteRequest leaves votedFor unchanged
#guard (voteGranted voter33 none 5 3 2 == false) &&
       (processVoteRequest s1 voter33 5 1 3 2).votedFor == none

-- Higher-term grant: term is bumped and votedFor is set
#guard (processVoteRequest s1 voter33 5 2 4 3).currentTerm == 2 &&
       (processVoteRequest s1 voter33 5 2 4 3).votedFor == some 5

-- Higher-term deny: term is bumped but votedFor is cleared
#guard (processVoteRequest s1 voter33 5 2 2 1).currentTerm == 2 &&
       (processVoteRequest s1 voter33 5 2 2 1).votedFor == none

-- processVoteRequest is consistent with wonInTerm: after all voters grant vote, candidate wins
-- 3-voter cluster [1,2,3], all grant vote to candidate 5 in term 1
-- (we use a record function that reflects 2 grants, which is a majority)
#guard wonInTerm [1, 2, 3]
    (fun t v => if t == 1 && (v == 1 || v == 2) then some 5 else none) 1 5 == true

end FVSquad.ElectionCorrespondence
