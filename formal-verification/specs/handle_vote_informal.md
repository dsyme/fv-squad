# Informal Specification: `handle_vote` — MsgRequestVote / MsgRequestPreVote

**Source**: `src/raft.rs` — `RaftCore::step`, the
`MessageType::MsgRequestVote | MessageType::MsgRequestPreVote` arm (lines ≈ 1485–1530).

**Related functions**: `RaftLog::is_up_to_date`, `get_priority`,
`vote_resp_msg_type`, `maybe_commit_by_vote`, `RaftCore::become_follower`.

---

## Purpose

When a node receives a request to vote for a candidate (real election or
pre-election), it must decide whether to grant the vote. The decision follows the
Raft safety rules plus two extensions specific to this implementation:

1. **Priority-based tiebreaking** — a node may withhold a vote if it is not
   behind the candidate AND its own priority is higher.
2. **Leader-lease protection** — a node that recently heard from a known leader
   refuses to disrupt the cluster by granting a vote (unless the request was
   explicitly forced by a leader-transfer operation).

A `MsgRequestVote` is a **real** vote that commits the node to a particular
candidate for the term (recorded in `self.vote`).  
A `MsgRequestPreVote` is a **pre-vote** — a dry-run that does *not* update the
node's term or `vote` field, used to prevent stale nodes from disrupting the
leader.

---

## Preconditions

* The function is called only after the term-handling prelude in `step()` has
  already run.  By the time this arm is reached, one of the following holds:
  * `m.term == self.term` (message is in the current term), **or**
  * `m.term > self.term` **and** `self.term` has already been updated to
    `m.term` and `become_follower(m.term, INVALID_ID)` was called (for real
    votes), **or**
  * `m.term > self.term` **and** the lease check suppressed the term update
    and the function returned early (`return Ok(())`), so this arm is never
    reached in that case.
* Lease-suppressed early returns only happen for `m.term > self.term` when
  `check_quorum && leader_id != INVALID_ID && election_elapsed < election_timeout`
  and the request is not a leader-transfer campaign.
* For `MsgRequestPreVote`, term is never updated.

---

## The `can_vote` Predicate

A node grants a vote (sends `reject = false`) if and only if **all three** of the
following conditions hold:

### Condition 1 — Willingness (`can_vote`)

```
can_vote :=
     (self.vote == m.from)               -- repeat of an already-cast vote
  || (self.vote == INVALID_ID            -- haven't voted yet
         && self.leader_id == INVALID_ID)    -- and don't see a live leader
  || (m.type == MsgRequestPreVote        -- OR: pre-vote for a future term
         && m.term > self.term)
```

Key semantics:
- The first clause handles **idempotent re-requests**: if the node already voted
  for this candidate (possibly in a prior message loss/retry), it will vote again.
- The second clause captures the normal first-vote case. The `leader_id` guard
  prevents vote-splitting when a leader is still in contact (conservative).
- The third clause makes pre-votes permissive across term boundaries: a node that
  already sees a leader in the current term can still reply positively to a
  pre-vote for a higher term (it won't commit to it though).

### Condition 2 — Log up-to-date (`is_up_to_date`)

```
is_up_to_date(m.index, m.log_term) :=
     m.log_term > self.raft_log.last_term()
  || (m.log_term == self.raft_log.last_term() && m.index >= self.raft_log.last_index())
```

The candidate's log must be at least as up-to-date as the voter's log. This is
the Raft safety invariant that prevents data loss.

### Condition 3 — Priority (`priority_ok`)

```
priority_ok :=
     m.index > self.raft_log.last_index()   -- candidate is ahead: always ok
  || self.priority <= get_priority(&m)      -- equal priority: not higher-priority
```

Where `get_priority(m)` returns `m.priority` if non-zero, else
`i64::try_from(m.deprecated_priority).unwrap_or(i64::MAX)`.

This extension prevents a high-priority node from granting a vote to a
lower-priority candidate when the two have the same last index (are tied in log
length). If the candidate is strictly ahead in the log, priority is irrelevant.

---

## Postconditions

### Case A — Vote Granted (`can_vote && is_up_to_date && priority_ok`)

1. **Response sent** with `reject = false` and `term = m.term` (not `self.term`;
   important for pre-votes where self.term may lag).
2. **For real votes (`MsgRequestVote`) only**:
   - `self.vote = m.from`   — the node is now committed for this term
   - `self.election_elapsed = 0`   — election timer is reset
3. **For pre-votes**: neither `self.vote` nor `self.election_elapsed` are changed.

### Case B — Vote Rejected (`¬can_vote || ¬is_up_to_date || ¬priority_ok`)

1. **Response sent** with `reject = true` and `term = self.term` (local term,
   which may differ from m.term for pre-votes).
2. **Commit hint** included: `to_send.commit = self.raft_log.committed` and
   `to_send.commit_term = raft_log.last_entry_term_in_range(committed)` — allows
   the rejected candidate to fast-forward its commit index.
3. **`maybe_commit_by_vote`** is called: if the vote message carries a valid
   `commit` index greater than the current `committed`, the node may advance its
   own commit index without requiring a normal `MsgAppend`. (This is an
   optimisation to speed up convergence after a leader election.)

---

## Invariants

1. **At-most-one-vote-per-term**: A node sets `self.vote = m.from` at most once
   per term. Once set (to a non-INVALID_ID value), subsequent real vote requests
   for the same term are only approved if `m.from == self.vote` (the idempotent
   re-vote clause). Requests from any other candidate are rejected.
   * This is the core Raft safety invariant.
   * Already formalised in `FVSquad/VoteCommitment.lean`.

2. **Response term**: the response term equals `m.term` for approvals, and
   `self.term` for rejections. This ensures the candidate can detect stale
   responses.

3. **Pre-vote non-commitment**: handling `MsgRequestPreVote` never mutates
   `self.vote`, `self.term`, or `self.election_elapsed`.

4. **Election timer reset only on approval**: `election_elapsed` is reset to `0`
   only when a real vote is granted. Rejections do not reset the timer.

5. **No vote to lower-priority tied candidate**: if the voter has higher priority
   than the candidate and neither is ahead in the log, the vote is denied. This
   prevents lower-priority nodes from winning elections unnecessarily.

---

## Edge Cases

* **Same candidate, same term, repeat request**: granted again (idempotent).
* **Different candidate, same term**: rejected (`self.vote != INVALID_ID && self.vote != m.from`).
* **Candidate ahead in term but behind in log** (`is_up_to_date = false`): rejected
  even if `can_vote` is true.
* **Priority tie (`self.priority == get_priority(m)`)**: vote granted if
  `is_up_to_date` holds (priority equal → `priority_ok` is true by `<=`).
* **Leader-lease**: if `check_quorum && leader_id != INVALID_ID && elapsed < timeout`
  and `m.term > self.term` and not a leader-transfer, the function returns early
  *before* reaching this arm — the vote is silently dropped, no response sent.
* **`maybe_commit_by_vote` with `m.commit = 0`**: no-op (guarded at the top of
  that function).
* **Candidate already at state Leader**: `maybe_commit_by_vote` explicitly skips
  commit advancement for leaders.

---

## Examples

| Scenario | `can_vote` | `is_up_to_date` | `priority_ok` | Outcome |
|---|---|---|---|---|
| Haven't voted, no leader, log equal | ✅ | ✅ | ✅ (tie) | Grant |
| Already voted for same candidate | ✅ | depends | depends | Grant if up-to-date |
| Already voted for different candidate | ❌ | — | — | Reject |
| Candidate behind in log term | ✅ | ❌ | — | Reject |
| Pre-vote for future term, already sees leader | ✅ (3rd clause) | ✅ | ✅ | Grant |
| Lower-priority candidate, log tied | ✅ | ✅ | ❌ | Reject |
| Candidate one entry ahead, self has higher priority | ✅ | ✅ | ✅ (ahead) | Grant |

---

## Open Questions

1. **Leader-lease and pre-vote**: The lease check happens in the term-handling
   prelude only for `m.term > self.term`. For `m.term == self.term`, a pre-vote
   request passes through directly. Is this intentional? Could a pre-vote in the
   current term disrupt a live leader's followers?

2. **`maybe_commit_by_vote` safety**: When can the commit-fast-forward in
   `maybe_commit_by_vote` cause a follower to advance its `committed` index
   beyond what the current leader knows about? Is there a risk of divergence?

3. **Priority overflow in `get_priority`**: `m.deprecated_priority` is `u64`,
   cast to `i64` with a fallback to `i64::MAX`. Could a legitimate `u64` value
   > `i64::MAX` inadvertently give `i64::MAX` priority, winning elections
   incorrectly?  (This was already flagged in `FVSquad/GetPriority.lean`.)

4. **`can_vote` third clause (pre-vote for future term)**: When `self.vote != INVALID_ID`
   (i.e., already voted for some other candidate in the current term) AND the
   pre-vote is for `m.term > self.term`, `can_vote` is `true` via the third
   clause. Is it correct to allow a pre-vote grant even when committed to another
   candidate in the current term? This seems intentional (pre-vote doesn't commit
   anything), but warrants a comment.

---

## Approach for Lean Formalisation (Phase 3+)

**Key types to define:**
- `VoteRequest`: `{ from : NodeId, term : Term, log_index : Nat, log_term : Term, priority : Int, is_pre_vote : Bool, is_transfer : Bool }`
- `VoterState`: `{ term : Term, vote : Option NodeId, leader_id : Option NodeId, election_elapsed : Nat, election_timeout : Nat, check_quorum : Bool, last_log_term : Term, last_log_index : Nat, priority : Int }`
- `VoteResponse`: `{ reject : Bool, term : Term, commit : Nat, commit_term : Term }`

**Key propositions:**
1. `at_most_one_vote_per_term`: if `can_vote_grant s req`, then either `s.vote = none` or `s.vote = some req.from`
2. `vote_response_term_correct`: approval → term = req.term; rejection → term = s.term
3. `pre_vote_does_not_commit`: after handling a pre-vote, `s'.vote = s.vote ∧ s'.term = s.term ∧ s'.election_elapsed = s.election_elapsed`
4. `grant_implies_up_to_date`: vote granted → `is_up_to_date s req`
5. `election_timer_reset_only_on_real_grant`: `s'.election_elapsed = 0 ↔ ¬req.is_pre_vote ∧ granted`

🔬 *Lean Squad — automated formal specification.*
