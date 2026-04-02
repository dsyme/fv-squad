# Informal Specification: `ProgressTracker::tally_votes`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

## Source

`src/tracker.rs`, function `ProgressTracker::tally_votes` (lines ~301–321).

## Purpose

`tally_votes` counts the yes-votes and no-votes cast so far by the **current voters**
and combines them with an overall `VoteResult` determination. It is called to track
progress of an election: a leader can log `"received N granted, M rejected votes out of
total..."` for monitoring, and the `VoteResult` drives the election outcome.

The function returns a triple `(granted, rejected, result)`:
- `granted`: number of current voters that voted `true` (yes).
- `rejected`: number of current voters that voted `false` (no).
- `result`: the overall `VoteResult` (Won / Pending / Lost) determined by `vote_result`.

## Preconditions

- `self.conf.voters` is the set of current voter IDs (a `JointConfig`).
- `self.votes` is a `HashMap<u64, bool>` mapping peer IDs to their vote.
- Both can be empty. Non-voter entries in `votes` are silently ignored.

## Postconditions

1. `granted` = number of peer IDs that are both in `voters` AND voted `true`.
2. `rejected` = number of peer IDs that are both in `voters` AND voted `false`.
3. `result` = `self.vote_result(&self.votes)`, which in turn calls
   `self.conf.voters.vote_result(|id| votes.get(&id).cloned())`.
4. `granted + rejected ≤ |voters|` (bounded by the voter count).
5. `granted + rejected + missing = |voters|` where `missing` = voters that have not
   yet cast a vote.

## Invariants

- Non-voter IDs in `votes` do not affect `granted`, `rejected`, or `result`.
- `result` is fully determined by the `votes` of current voters only.
- If `granted ≥ majority(|voters|)` then `result = Won`.
- If `rejected ≥ majority(|voters|)` then `result = Lost` (the remaining voters
  cannot form a yes-quorum even if all vote yes).

## Key property: rejection implies loss

This is the most important invariant. If `rejected ≥ majority(n)`:
- The remaining voters that *could* still vote yes = `|voters| - rejected`.
- `|voters| - rejected ≤ |voters| - majority(|voters|) < majority(|voters|)`,
  because `|voters| < 2 × majority(|voters|)` for all n (since `majority(n) = n/2 + 1`).
- So even if every remaining voter (granted + missing) votes yes, there aren't enough
  to reach the quorum. Hence the result is definitively `Lost`.

## Edge cases

- **Empty voters**: returns `(0, 0, Won)` (by the empty-quorum convention used throughout
  the codebase to make joint quorums work correctly with one empty half).
- **All voted yes**: `granted = |voters|`, `rejected = 0`, `result = Won`.
- **All voted no**: `granted = 0`, `rejected = |voters|`, `result = Lost`.
- **Nobody voted yet**: `granted = 0`, `rejected = 0`, `result = Pending`.
- **Votes from non-voters**: only current voters matter; stale or foreign entries in
  the votes map are ignored.

## Examples

| voters | votes | granted | rejected | result |
|--------|-------|---------|----------|--------|
| {1,2,3} | {1:yes,2:yes} | 2 | 0 | Won (2 ≥ 2 = majority(3)) |
| {1,2,3} | {1:yes,2:no} | 1 | 1 | Pending (1 < 2, 1+1 ≥ 2) |
| {1,2,3} | {1:no,2:no} | 0 | 2 | Lost (2 ≥ 2 = majority(3)) |
| {1,2,3} | {} | 0 | 0 | Pending (0 < 2, 0+3 ≥ 2) |
| {} | {1:yes} | 0 | 0 | Won (empty voters convention) |
| {1,2,3} | {4:yes,5:yes,1:yes} | 1 | 0 | Pending (non-voters 4,5 ignored) |

## Inferred intent

The `granted` and `rejected` counts are used primarily for logging/observability —
the informational output of how the vote is progressing. The `result` drives actual
behaviour (whether the candidate advances to leader, keeps campaigning, or gives up).

The function deliberately ignores non-voter entries in `votes` even though `vote_result`
does so implicitly. The comment in the code ("doesn't really matter in the way the
numbers are used") confirms that the counts are informational, not used for correctness.

## Open questions

1. Should `tally_votes` also filter votes against the **outgoing** quorum in a joint
   config (or only the incoming)? Currently it iterates over `self.votes` and checks
   `self.conf.voters.contains(id)` which checks the full `JointConfig`. This appears
   intentional so that joint-config membership is handled correctly.
2. In a joint configuration, a voter may be in both the incoming and outgoing set.
   Would `granted` count them twice? Looking at the code: it iterates `self.votes`
   (keyed by unique peer ID), so each peer is counted at most once regardless of which
   quorum half they are in. This seems correct but worth confirming with maintainers.
