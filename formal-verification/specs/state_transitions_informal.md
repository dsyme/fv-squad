# Informal Specification: Raft State Role Transitions

> 🔬 *Lean Squad — informal specification for formal verification.*
>
> **Target**: `become_follower`, `become_candidate`, `become_leader` (and `become_pre_candidate`)
> **Source**: `src/raft.rs`, lines ~1148–1280

---

## Purpose

These four functions control the Raft state role transitions. Together they implement the core Raft state machine:

```
Follower ←─────────────────────────────────────────────┐
    │                                                   │
    │  begin_campaign / become_candidate                │
    ↓                                                   │
Candidate ─(optional)→ PreCandidate                     │ become_follower
    │                                                   │
    │  poll() == Won / become_leader                    │
    ↓                                                   │
Leader ────────────────────────────────────────────────►┘
```

**Safety invariant**: A node must have the highest term in the cluster before becoming leader. This is enforced transitively: `become_candidate` increments `term`, `reset` clears `vote` on term change, and only a node that has collected a quorum of votes (with `vote = self.id` cast at `become_candidate`) can call `become_leader`.

---

## `become_follower(term: u64, leader_id: u64)`

### Preconditions
- None (callable from any state)

### Postconditions
1. `self.state = StateRole::Follower`
2. `self.term` = max(prior_term, `term`) — effectively `term` (caller ensures monotonicity)
3. `self.vote` = `INVALID_ID` iff `term ≠ prior_term` (via `reset(term)`)
4. `self.leader_id` = `leader_id`
5. `self.raft_log.max_apply_unpersisted_log_limit` = 0 (hardcoded for now)
6. All other fields reset via `reset(term)`: `election_elapsed = 0`, `heartbeat_elapsed = 0`,
   `pending_conf_index = 0`, `read_only` cleared, `leader_transfer` aborted, votes reset

### Invariants
- **Term monotonicity**: If `term ≥ self.term` then `self.term` after = `term`.
  In practice callers always pass `term ≥ current_term` or `term = current_term`.
- If `term = self.term` (same-term demotion), vote is **preserved** (not cleared).

### Edge cases
- `leader_id = INVALID_ID (0)`: this is the normal case when the leader is unknown
  (e.g., split-brain recovery, timeout)
- `term < self.term`: this can happen but is unusual; `reset(term)` would then
  **downgrade** the term, clearing vote. (Open question: is this ever correct?)

---

## `become_candidate()`

### Preconditions
- `self.state ≠ StateRole::Leader` (assert in production code; panic otherwise)

### Postconditions
1. `self.term` = prior_term + 1 (strict increment)
2. `self.vote` = `self.id` (self-vote cast immediately)
3. `self.state` = `StateRole::Candidate`
4. `self.leader_id` = `INVALID_ID` (via `reset`)
5. All other fields reset via `reset(term + 1)`: votes cleared, timeouts reset

### Invariants
- **Term increment**: `self.term` after = `self.term` before + 1
- **Self-vote**: `self.vote` = `self.id` (the node votes for itself in the new term)
- **Vote cleared on term change**: since `term + 1 ≠ old_term`, `reset` clears the old vote
  before the self-vote is recorded

### Edge cases
- Transition from `PreCandidate` to `Candidate`: allowed (no assert against it).
  This is the normal pre-vote → vote path.
- Transition from `Follower` to `Candidate`: the standard path.
- Called from `campaign()` during an election timeout.

---

## `become_leader()`

### Preconditions
- `self.state ≠ StateRole::Follower` (assert in production code; panic otherwise)
- Implies: called only from `Candidate` or `PreCandidate` state
- Invariant: the node must have won a quorum vote at `self.term` before calling this
  (maintained by the caller: `step_candidate` only calls `become_leader` when
  `self.poll(...)` returns `VoteResult::Won`)

### Postconditions
1. `self.state` = `StateRole::Leader`
2. `self.term` unchanged (= current `self.term` before the call)
3. `self.leader_id` = `self.id` (node identifies itself as leader)
4. `self.vote` unchanged iff `term = self.term` (the vote for self is preserved)
5. `self.uncommitted_state.uncommitted_size` = 0
6. `self.uncommitted_state.last_log_tail_index` = `self.raft_log.last_index()`
7. `self.raft_log.last_index()` after = prior `last_index()` + 1 (empty entry appended)
8. `self.pending_conf_index` = prior `last_index()` (conservative scan skip)
9. The node's own `Progress` entry switches to `Replicate` state

### Invariants
- **Leader uniqueness per term**: at most one node can be leader in a given term.
  This follows from: (a) `become_leader` requires winning a quorum of votes,
  (b) each node votes at most once per term (`vote_commitment` — proved in run 60).
  Together these establish election safety.
- **Term lock**: `become_leader` does not change `self.term`. So the leader's term
  equals the term at which it won the election.
- **Log tail**: the new leader immediately appends a no-op entry. After this,
  `last_index() = persisted + 1` (required by the assertion `last_index = persisted`
  before the append).

### Edge cases
- **Single-node cluster**: `self.poll(self_id, ..., true)` returns `Won` immediately
  in `campaign`, so `become_leader` is called directly from `campaign` without any
  `RequestVote` messages. `last_index = persisted` holds since there are no
  uncommitted entries.
- **Assert `last_index = persisted`**: this is a hard invariant; violating it would
  be a serious bug. The assertion checks that all prior log entries are persisted
  before becoming leader.

---

## `become_pre_candidate()`

### Preconditions
- `self.state ≠ StateRole::Leader` (assert; panic otherwise)

### Postconditions
1. `self.state` = `StateRole::PreCandidate`
2. `self.term` **unchanged** (pre-candidate does NOT increment term)
3. `self.vote` **unchanged** (pre-candidate does NOT change vote)
4. `self.leader_id` = `INVALID_ID`
5. Votes cleared in the progress tracker

### Invariants
- **No-term-change**: this is the key difference from `become_candidate`. Pre-vote
  messages are sent with `term + 1` (speculatively) but the node's actual term
  remains unchanged until it has collected a pre-vote quorum.

---

## Combined State Machine Properties

1. **Term monotonicity** (node): `self.term` never decreases across any transition.
   - `become_follower(t, _)`: sets term to `t`; caller ensures `t ≥ current_term`
   - `become_candidate()`: `term++`
   - `become_leader()`: term unchanged
   - `become_pre_candidate()`: term unchanged

2. **Vote monotonicity within a term**: once `self.vote` is set to some `v ≠ INVALID_ID`,
   it is only changed by a term change (reset). Formally:
   `self.vote = v ∧ v ≠ INVALID_ID → (next transition with same term → self.vote = v)`

3. **State role transitions**:
   - Follower → Candidate: via `become_candidate()`
   - Follower → PreCandidate: via `become_pre_candidate()`
   - Candidate → Leader: via `become_leader()`
   - PreCandidate → Candidate: via `become_candidate()`
   - Any → Follower: via `become_follower()`
   - **Forbidden**: Follower → Leader (asserted away in `become_leader`)
   - **Forbidden**: Leader → Candidate/PreCandidate (asserted away)

4. **Leader uniqueness** (election safety): follows from vote-commitment
   (`vote_commitment` in `VoteCommitment.lean`) + majority quorum intersection.
   Specifically: if node A is leader at term `t`, it won a quorum Q_A of votes,
   each of which set `vote = A.id` in that node's term-`t` state. For node B to
   also win at term `t`, it needs a disjoint quorum Q_B — but by quorum intersection,
   Q_A ∩ Q_B ≠ ∅, and any node in the intersection would have voted for both A and B
   at term `t`, contradicting the single-vote-per-term property.

---

## Approximations and Omissions

- The model omits I/O, logging, and error paths (none of the become_* functions return errors).
- The model omits the `pending_request_snapshot` preservation in `become_follower`.
- The `reset()` side effects on `Progress` entries are omitted in this specification
  (covered by the `ProgressTracking` target).
- The `uncommitted_state` update in `become_leader` is covered by the
  `UncommittedState` target.
- The no-op log entry appended by `become_leader` affects `raft_log` (covered by
  `RaftLogAppend` target).

---

## Open Questions

1. **Is `become_follower` with `term < current_term` a bug or a valid use case?**
   The implementation allows it (no assert), but it would downgrade the term, which
   seems unsafe. All callers in `raft.rs` appear to pass `term ≥ self.term`.

2. **Should `become_leader` assert `state = Candidate` rather than `state ≠ Follower`?**
   The current check allows `become_leader` from `PreCandidate` state, which would
   skip the voting phase entirely. Is this intentional for pre-vote optimization paths?

3. **The `last_index = persisted` assertion in `become_leader`**: what guarantees
   this holds in the pre-candidate → leader path? Is there a proof obligation here?

---

## Proposed Lean Target

**Lean file**: `formal-verification/lean/FVSquad/StateTransitions.lean`

**Key types**:
```lean
inductive StateRole | Follower | Candidate | Leader | PreCandidate

structure RaftState where
  state    : StateRole
  term     : Term          -- u64 (Nat)
  vote     : NodeId        -- INVALID_ID = 0 means no vote
  leaderId : NodeId        -- INVALID_ID = 0 means unknown leader

-- reset(t) semantics
def raftReset (s : RaftState) (t : Term) : RaftState :=
  { state := s.state, leaderId := 0,
    term := t, vote := if s.term ≠ t then 0 else s.vote }

def becomeCandidateState (s : RaftState) : RaftState :=
  let s' := raftReset s (s.term + 1)
  { s' with vote := s.id, state := .Candidate }

def becomeLeaderState (s : RaftState) : RaftState :=
  let s' := raftReset s s.term
  { s' with leaderId := s.id, state := .Leader }

def becomeFollowerState (s : RaftState) (t : Term) (lid : NodeId) : RaftState :=
  let s' := raftReset s t
  { s' with leaderId := lid, state := .Follower }
```

**Key propositions to prove**:
- `PROP-1`: `becomeCandidateState` increments term: `s'.term = s.term + 1`
- `PROP-2`: `becomeCandidateState` self-votes: `s'.vote = s.id`
- `PROP-3`: `becomeLeaderState` preserves term: `s'.term = s.term`
- `PROP-4`: `becomeLeaderState` sets leader: `s'.leaderId = s.id`
- `PROP-5`: `becomeFollowerState` sets state to Follower
- `PROP-6`: Term monotonicity: `s.term ≤ t → (becomeFollowerState s t lid).term = t`
- `PROP-7`: Vote cleared on term change: `s.term ≠ t → (becomeFollowerState s t lid).vote = 0`
- `PROP-8`: Vote preserved on same-term demotion: `(becomeFollowerState s s.term lid).vote = s.vote`
- `PROP-9`: After `becomeCandidateState`, prior vote cleared if different term (monotone)
- `PROP-10`: Transition guard: `becomeLeaderState` requires `state ≠ Follower` (modelled as precondition)
- `PROP-11`: Election safety (combined with VoteCommitment): at most one leader per term

> 🔬 *Generated by Lean Squad (run 61, 2026-03-22)*
