# Informal Specification: `election_model`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Target A1** — Foundation for closing the Raft election proof gap.

Source: `src/raft.rs` (primary), `src/tracker.rs` (tally), `src/quorum/majority.rs` (quorum)

---

## Purpose

The election model captures the pure state-transition logic governing how a Raft
node moves among the roles Follower → Candidate → Leader (and optionally through
PreCandidate), and how vote requests are granted or rejected.  The goal is a Lean
model that is expressive enough to discharge the five abstract hypotheses in
`RaftReachable.step` that are currently left as axioms.

---

## Node State

A node's persistent election-relevant state consists of:

| Field | Type | Meaning |
|-------|------|---------|
| `term` | `u64` | Monotonically increasing election term |
| `vote` | `u64` | ID of the candidate this node voted for (0 = not voted) |
| `state` | `StateRole` | `Follower \| Candidate \| Leader \| PreCandidate` |

`StateRole` is an enum defined in `src/raft.rs`:

```rust
pub enum StateRole {
    Follower,
    Candidate,
    Leader,
    PreCandidate,
}
```

---

## Preconditions (per-transition)

### `become_follower(term, leader_id)`
- **Pre**: `term >= self.term`  (Raft monotonicity rule: never decrease term)
- **Effect**: `self.term ← term`, `self.vote ← INVALID_ID` if `term > self.term`, state ← Follower

### `become_candidate()`
- **Pre**: `self.state ≠ Leader`  (leader cannot directly become candidate)
- **Effect**: `self.term ← self.term + 1`, `self.vote ← self.id`, state ← Candidate

### `become_leader()`
- **Pre**: `self.state ∈ {Candidate, PreCandidate}`  (follower cannot become leader directly)
- **Effect**: state ← Leader; term unchanged

---

## Vote-Granting Rules

A node grants a `MsgRequestVote` from candidate `c` with term `cTerm` and log
(last_index, last_term) = `(cIdx, cLogTerm)` **if and only if**:

1. **Term freshness**: `cTerm ≥ self.term`
2. **Vote availability**: one of:
   - (a) `self.vote = c` (already voted for this candidate — idempotent), or
   - (b) `self.vote = INVALID_ID` **and** `self.leader_id = INVALID_ID` (haven't voted yet, no known leader)
3. **Log up-to-date**: `is_up_to_date(cIdx, cLogTerm)` — the candidate's log is at least
   as up-to-date as the voter's (using last-log-term dominance, then length tiebreak)
4. **Priority gate** (optional): if `cIdx ≤ self.raft_log.last_index()`, the candidate's
   priority must be ≥ the voter's own priority

When a vote is granted for a regular `MsgRequestVote`:
- `self.vote ← c`
- `self.election_elapsed ← 0`

For `MsgRequestPreVote` the vote is not recorded (state unchanged), but the same
freshness and log checks apply with `m.term > self.term` used instead of `m.term ≥ self.term`.

---

## Key Invariants

### I1 — Term Monotonicity
For every node `n`:
```
∀ t₁ t₂, n observes term t₁ before t₂ → t₁ ≤ t₂
```
A node never decreases its own term.  `become_candidate` increments by exactly 1.

### I2 — Vote Uniqueness per Term
Each node grants at most one vote per term:
```
∀ n t c₁ c₂, n voted for c₁ in term t ∧ n voted for c₂ in term t → c₁ = c₂
```
Once `self.vote ≠ INVALID_ID` in a given term, no further vote can be granted in
that term unless the node advances to a new term (clearing its vote).

### I3 — Election Safety
At most one leader can win an election per term:
```
∀ t l₁ l₂, leader l₁ in term t ∧ leader l₂ in term t → l₁ = l₂
```
This follows from I2 + quorum intersection: two disjoint quorums would each need to
contain a node that voted for a different leader, but by I2 that is impossible.

### I4 — Leader Has Voted for Itself
If `n.state = Leader` and `n.term = t`, then `n.vote = n.id` in term `t` — the leader
voted for itself when campaigning.

### I5 — Log Freshness of Elected Leaders
Any node that wins an election has a log at least as up-to-date as a quorum of the
cluster at the time of the election (follows from the log-freshness vote condition).

---

## Postconditions

### After `become_candidate()`
- `self.term = old_term + 1`
- `self.vote = self.id`
- `self.state = Candidate`

### After `become_leader()`
- `self.state = Leader`
- `self.term` unchanged
- Leader appends a no-op entry to establish its commit authority

### After granting a vote (regular `MsgRequestVote`)
- `self.vote = m.from`
- `self.election_elapsed = 0`
- Term may have been updated if `m.term > self.term` (via `become_follower` called first)

---

## Edge Cases

- **Duplicate vote request**: if a node receives the same vote request again after
  already having voted for that candidate, it re-grants the vote (idempotent).
  The condition `self.vote == m.from` covers this.
- **Split vote**: if no candidate receives a quorum, the election times out and
  all candidates re-increment their term and start a new election.
- **Leadership transfer**: a leader can instruct a peer to campaign via
  `MsgTimeoutNow`, bypassing the election timeout.
- **PreVote optimization**: when enabled, a candidate first runs a pre-vote round
  without incrementing its term.  If the pre-vote wins a quorum, the candidate
  proceeds to a real election.  Term is only incremented on entering the real
  Candidate state.
- **Term higher than local**: if a node receives any message with a higher term
  than its own, it immediately reverts to Follower and updates its term
  (`become_follower(m.term, ...)`).

---

## Examples

### Successful election (3 nodes, no pre-vote)

| Step | Node | Action | term | vote | state |
|------|------|--------|------|------|-------|
| 1 | N1 | Election timeout, `become_candidate()` | 1→2 | N1 | Candidate |
| 2 | N1 | Sends `MsgRequestVote{term=2}` to N2, N3 | | | |
| 3 | N2 | Receives vote, grants (log ok, no prior vote) | 2 | N1 | Follower |
| 4 | N1 | Receives N2's grant, polls tracker: quorum → `become_leader()` | 2 | N1 | Leader |

### Vote rejected (stale log)

| Step | Node | Action | Result |
|------|------|--------|--------|
| 1 | N2 | already has entries at term 2 index 10 | |
| 2 | N1 | sends `MsgRequestVote{term=3, last_log=(term=1, idx=5)}` | |
| 3 | N2 | `is_up_to_date(5, 1)` → false (N2 has term=2 last) | Reject |

---

## Approximations for Lean Model

- **No I/O or network**: the Lean model represents a single node's local state
  transitions; message sending is abstracted away (not modelled).
- **No Inflights**: the progress ring buffer is irrelevant to election safety.
- **No configuration changes during election**: joint-consensus transitions that
  overlap with an election are not modelled; we assume a fixed voter set.
- **Nat / Fin instead of u64**: Lean `Nat` is used for term and IDs; overflow is
  impossible in the model but must be noted as omitted.
- **No `pre_vote` flag**: the model may initially focus on the non-pre-vote path.
  Pre-vote can be added as an extension once the core invariants are proved.

---

## Open Questions

1. **Priority gate**: the `self.priority ≤ get_priority(m)` check is a non-standard
   extension of Raft (TiKV addition).  Should the formal model include it, or abstract
   it away?  If included, priority must become a node attribute.
2. **Pre-vote**: should `PreCandidate` be in the initial Lean model, or deferred?
3. **Quorum vs. joint quorum**: does the initial model need to handle joint consensus
   (`JointConfig`) or only simple majority quorums?
4. **Log model coupling**: vote-granting requires `is_up_to_date`, which is already
   proved in `FVSquad/IsUpToDate.lean`.  How tightly should the election model
   couple to the log model?

---

## Connection to Existing Lean Files

| Existing file | Provides |
|--------------|----------|
| `FVSquad/MajorityVote.lean` | `VoteResult` (Won/Lost/Pending), vote counting |
| `FVSquad/IsUpToDate.lean` | `isUpToDate` — log freshness predicate for vote-granting |
| `FVSquad/TallyVotes.lean` | `tallyVotes` — tracker-level vote aggregation |
| `FVSquad/RaftTrace.lean` | `step` with 5 abstract hypotheses awaiting discharge |
| `FVSquad/AEBroadcastInvariant.lean` | `hqc_preserved` (partially discharges `step` HQ) |

The election model formalises the `NodeState` and transition function; together
with `TallyVotes` and `MajorityVote` this should suffice to discharge hypotheses
`hvote_unique` and `hqc_preserved` in `RaftReachable.step`.

> 🔬 Generated by Lean Squad automated formal verification (Run 97).
