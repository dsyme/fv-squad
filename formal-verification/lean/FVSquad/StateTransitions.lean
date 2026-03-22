/-!
# State Role Transitions — Lean 4 Specification and Proofs

Models the Raft state role transitions: `become_follower`, `become_candidate`,
`become_leader`, and `become_pre_candidate`.

Relevant Rust code in `src/raft.rs`:
- `become_follower(term, leader_id)` lines ~1148–1175
- `become_candidate()` lines ~1176–1198
- `become_pre_candidate()` lines ~1199–1225
- `become_leader()` lines ~1226–1276 (log / uncommitted-state parts omitted)

## Key safety invariant

A node must hold the highest term in the cluster before it can become leader.
Enforced transitively:
1. `become_candidate` increments `term` and self-votes.
2. `become_leader` requires winning a quorum (caller's responsibility).
3. At most one vote is cast per term (proved in `VoteCommitment.lean`).
4. Quorum intersection ⇒ at most one leader per term (election safety).

## Model scope and approximations

* `NodeId` and `Term` are modelled as `Nat` (Rust `u64`; 64-bit bound omitted).
* `INVALID_ID = 0` (no real node has this ID in a well-configured cluster).
* `RaftState` is reduced to the fields relevant to role transitions:
  `id`, `state`, `term`, `vote`, `leaderId`.
* The following are **omitted** (handled by other targets):
  - `raft_log` mutations in `become_leader` (no-op entry append) → `RaftLogAppend`
  - `uncommitted_state` reset in `become_leader`              → `UncommittedState`
  - `Progress` tracker resets in `reset()`                   → `ProgressTracking`
  - `read_only`, `pending_conf_index`, `election_elapsed`,
    `heartbeat_elapsed`, `leader_transfer` resets              → omitted
  - I/O, logging, error paths                                 → omitted

🔬 *Lean Squad — automated formal verification.*
-/

import Mathlib.Tactic

namespace FVSquad.StateTransitions

abbrev NodeId := Nat
abbrev Term   := Nat

/-- `INVALID_ID = 0` represents "no vote cast" or "unknown leader". -/
def INVALID_ID : NodeId := 0

/-- The four role states a Raft node can be in. -/
inductive StateRole where
  | Follower
  | Candidate
  | Leader
  | PreCandidate
  deriving Repr, DecidableEq

/-- Role-transition-relevant portion of a Raft node's state.
    Other fields (`raft_log`, `pending_conf_index`, etc.) are omitted. -/
structure RaftState where
  id       : NodeId    -- this node's own ID (immutable)
  state    : StateRole
  term     : Term
  vote     : NodeId    -- 0 = INVALID_ID (no vote cast this term)
  leaderId : NodeId    -- 0 = INVALID_ID (unknown leader)
  deriving Repr, DecidableEq

/-! ## Implementation model -/

/-- `raftReset(s, t)`: mirrors `RaftCore::reset(term)`.
    Always: sets `term := t` and `leaderId := INVALID_ID`.
    When the term changes (`s.term ≠ t`): also clears `vote`.
    When the term is unchanged: preserves `vote` (same-term demotion path). -/
def raftReset (s : RaftState) (t : Term) : RaftState :=
  { s with
      term     := t
      leaderId := INVALID_ID
      vote     := if s.term ≠ t then INVALID_ID else s.vote }

/-- `becomeFollowerState(s, t, lid)`: mirrors `become_follower(term, leader_id)`.
    Calls `raftReset(t)`, then sets `state = Follower` and `leaderId = lid`. -/
def becomeFollowerState (s : RaftState) (t : Term) (lid : NodeId) : RaftState :=
  let s' := raftReset s t
  { s' with state := .Follower, leaderId := lid }

/-- `becomeCandidateState(s)`: mirrors `become_candidate()`.
    Increments term (clearing old vote), then records self-vote. -/
def becomeCandidateState (s : RaftState) : RaftState :=
  let s' := raftReset s (s.term + 1)
  { s' with state := .Candidate, vote := s.id }

/-- `becomePreCandidateState(s)`: mirrors `become_pre_candidate()`.
    Does NOT change `term` or `vote` — only the role and `leaderId`. -/
def becomePreCandidateState (s : RaftState) : RaftState :=
  { s with state := .PreCandidate, leaderId := INVALID_ID }

/-- `becomeLeaderState(s)`: mirrors `become_leader()` (role/leaderId only).
    Calls `raftReset(s.term)` (same term → vote preserved), then sets
    `state = Leader` and `leaderId = s.id`.
    Log and uncommitted-state mutations are handled by other targets. -/
def becomeLeaderState (s : RaftState) : RaftState :=
  let s' := raftReset s s.term
  { s' with state := .Leader, leaderId := s.id }

/-! ## Helper lemmas -/

/-- `raftReset` when the term changes: clears `vote`. -/
private lemma raftReset_ne {s : RaftState} {t : Term} (h : s.term ≠ t) :
    raftReset s t =
      { s with term := t, leaderId := INVALID_ID, vote := INVALID_ID } := by
  simp [raftReset, h]

/-- `raftReset` when the term is unchanged: preserves `vote`, clears `leaderId`. -/
private lemma raftReset_eq (s : RaftState) :
    raftReset s s.term = { s with leaderId := INVALID_ID } := by
  simp [raftReset]

/-- `s.term ≠ s.term + 1` for natural numbers. -/
private lemma ne_succ_self (n : Nat) : n ≠ n + 1 :=
  Nat.ne_of_lt (Nat.lt_succ_self n)

/-- Structural lemma for `becomeCandidateState`. -/
private lemma becomeCandidateState_eq (s : RaftState) :
    becomeCandidateState s =
      { s with term := s.term + 1, leaderId := INVALID_ID,
               vote := s.id, state := .Candidate } := by
  unfold becomeCandidateState
  rw [raftReset_ne (ne_succ_self s.term)]

/-- Structural lemma for `becomeLeaderState`. -/
private lemma becomeLeaderState_eq (s : RaftState) :
    becomeLeaderState s = { s with state := .Leader, leaderId := s.id } := by
  unfold becomeLeaderState
  rw [raftReset_eq]

/-! ## Propositions: `become_candidate` -/

/-- PROP-1  `becomeCandidateState` increments the term by exactly 1. -/
theorem becomeCandidate_term (s : RaftState) :
    (becomeCandidateState s).term = s.term + 1 := by
  simp [becomeCandidateState_eq]

/-- PROP-2  `becomeCandidateState` records a self-vote. -/
theorem becomeCandidate_selfvote (s : RaftState) :
    (becomeCandidateState s).vote = s.id := by
  simp [becomeCandidateState_eq]

/-- PROP-3  `becomeCandidateState` sets `state = Candidate`. -/
theorem becomeCandidate_state (s : RaftState) :
    (becomeCandidateState s).state = .Candidate := by
  simp [becomeCandidateState_eq]

/-- PROP-4  `becomeCandidateState` clears `leaderId`. -/
theorem becomeCandidate_leaderId (s : RaftState) :
    (becomeCandidateState s).leaderId = INVALID_ID := by
  simp [becomeCandidateState_eq]

/-- PROP-5  `becomeCandidateState` strictly increases the term. -/
theorem becomeCandidate_term_increases (s : RaftState) :
    s.term < (becomeCandidateState s).term := by
  simp [becomeCandidateState_eq]

/-- PROP-6  `becomeCandidateState` preserves the node's own `id`. -/
theorem becomeCandidate_id_preserved (s : RaftState) :
    (becomeCandidateState s).id = s.id := by
  simp [becomeCandidateState_eq]

/-- PROP-7  After `becomeCandidateState`, the node is not yet a leader. -/
theorem becomeCandidate_not_leader (s : RaftState) :
    (becomeCandidateState s).state ≠ .Leader := by
  simp [becomeCandidateState_eq]

/-! ## Propositions: `become_leader` -/

/-- PROP-8  `becomeLeaderState` preserves the term (no increment). -/
theorem becomeLeader_term_preserved (s : RaftState) :
    (becomeLeaderState s).term = s.term := by
  simp [becomeLeaderState_eq]

/-- PROP-9  `becomeLeaderState` sets `leaderId = s.id`. -/
theorem becomeLeader_leaderId (s : RaftState) :
    (becomeLeaderState s).leaderId = s.id := by
  simp [becomeLeaderState_eq]

/-- PROP-10  `becomeLeaderState` sets `state = Leader`. -/
theorem becomeLeader_state (s : RaftState) :
    (becomeLeaderState s).state = .Leader := by
  simp [becomeLeaderState_eq]

/-- PROP-11  `becomeLeaderState` preserves the vote (same-term `raftReset`). -/
theorem becomeLeader_vote_preserved (s : RaftState) :
    (becomeLeaderState s).vote = s.vote := by
  simp [becomeLeaderState_eq]

/-- PROP-12  `becomeLeaderState` does not demote to follower. -/
theorem becomeLeader_not_follower (s : RaftState) :
    (becomeLeaderState s).state ≠ .Follower := by
  simp [becomeLeaderState_eq]

/-! ## Propositions: `become_follower` -/

/-- PROP-13  `becomeFollowerState` sets `state = Follower`. -/
theorem becomeFollower_state (s : RaftState) (t : Term) (lid : NodeId) :
    (becomeFollowerState s t lid).state = .Follower := by
  simp [becomeFollowerState]

/-- PROP-14  `becomeFollowerState` sets the term to `t`. -/
theorem becomeFollower_term (s : RaftState) (t : Term) (lid : NodeId) :
    (becomeFollowerState s t lid).term = t := by
  simp [becomeFollowerState, raftReset]

/-- PROP-15  `becomeFollowerState` sets `leaderId = lid`. -/
theorem becomeFollower_leaderId (s : RaftState) (t : Term) (lid : NodeId) :
    (becomeFollowerState s t lid).leaderId = lid := by
  simp [becomeFollowerState, raftReset]

/-- PROP-16  `becomeFollowerState` clears `vote` when the term changes. -/
theorem becomeFollower_vote_cleared (s : RaftState) (t : Term) (lid : NodeId)
    (h : s.term ≠ t) : (becomeFollowerState s t lid).vote = INVALID_ID := by
  simp [becomeFollowerState, raftReset_ne h]

/-- PROP-17  `becomeFollowerState` preserves `vote` on same-term demotion
    (e.g., a leader steps down but keeps its vote-for-self). -/
theorem becomeFollower_vote_same_term (s : RaftState) (lid : NodeId) :
    (becomeFollowerState s s.term lid).vote = s.vote := by
  simp [becomeFollowerState, raftReset_eq]

/-- PROP-18  Term monotonicity: if the caller passes `t ≥ s.term`, the term
    does not decrease (callers always satisfy this in well-formed Raft). -/
theorem becomeFollower_term_mono (s : RaftState) (t : Term) (lid : NodeId)
    (h : s.term ≤ t) : s.term ≤ (becomeFollowerState s t lid).term := by
  simp [becomeFollower_term]; exact h

/-! ## Propositions: `become_pre_candidate` -/

/-- PROP-19  `becomePreCandidateState` sets `state = PreCandidate`. -/
theorem becomePreCandidate_state (s : RaftState) :
    (becomePreCandidateState s).state = .PreCandidate := by
  simp [becomePreCandidateState]

/-- PROP-20  `becomePreCandidateState` does NOT change the term. -/
theorem becomePreCandidate_term_unchanged (s : RaftState) :
    (becomePreCandidateState s).term = s.term := by
  simp [becomePreCandidateState]

/-- PROP-21  `becomePreCandidateState` does NOT change the vote. -/
theorem becomePreCandidate_vote_unchanged (s : RaftState) :
    (becomePreCandidateState s).vote = s.vote := by
  simp [becomePreCandidateState]

/-- PROP-22  `becomePreCandidateState` clears `leaderId`. -/
theorem becomePreCandidate_leaderId (s : RaftState) :
    (becomePreCandidateState s).leaderId = INVALID_ID := by
  simp [becomePreCandidateState]

/-! ## Combined / cross-transition properties -/

/-- PROP-23  Follower → Candidate → Follower: the final term equals the
    candidate's incremented term (not the original term). -/
theorem candidate_then_follower_term (s : RaftState) (lid : NodeId) :
    let c := becomeCandidateState s
    (becomeFollowerState c c.term lid).term = s.term + 1 := by
  simp [becomeCandidate_term, becomeFollower_term]

/-- PROP-24  Candidate's vote is cleared from the old term (the self-vote
    is in the *new* term, so becoming a follower at an even newer term clears it). -/
theorem candidate_follower_newer_term_clears_vote
    (s : RaftState) (t : Term) (lid : NodeId)
    (h : s.term + 1 ≠ t) :
    (becomeFollowerState (becomeCandidateState s) t lid).vote = INVALID_ID := by
  apply becomeFollower_vote_cleared
  simp [becomeCandidate_term]
  exact h

/-- PROP-25  Becoming a follower always yields `state = Follower`, regardless
    of the starting role. -/
theorem any_to_follower (s : RaftState) (t : Term) (lid : NodeId) :
    (becomeFollowerState s t lid).state = .Follower :=
  becomeFollower_state s t lid

/-- PROP-26  Two successive `becomeFollower` calls with the same term are
    equivalent to the second call alone (idempotence in role). -/
theorem becomeFollower_idempotent_role (s : RaftState) (t : Term)
    (lid1 lid2 : NodeId) :
    (becomeFollowerState (becomeFollowerState s t lid1) t lid2).state = .Follower := by
  simp [becomeFollower_state]

/-- PROP-27  `raftReset` is idempotent: resetting twice to the same term is a
    no-op on the second call. -/
theorem raftReset_idempotent (s : RaftState) (t : Term) :
    raftReset (raftReset s t) t = raftReset s t := by
  simp only [raftReset, ne_eq, not_not]
  -- After the first reset, (raftReset s t).term = t, so t ≠ t is False.
  -- The second reset therefore takes the "same term" branch, preserving vote.
  ext <;> simp [raftReset]

/-- PROP-28  Becoming a pre-candidate and then a candidate yields `Candidate`
    state (the standard pre-vote → vote promotion path). -/
theorem preCandidate_then_candidate (s : RaftState) :
    (becomeCandidateState (becomePreCandidateState s)).state = .Candidate := by
  simp [becomeCandidate_state]

/-- PROP-29  In the pre-vote path the term seen by the cluster is `s.term + 1`
    (speculative), even though the node's stored term is `s.term` while in
    `PreCandidate` state.  After promotion to `Candidate`, the stored term
    catches up: `(becomeCandidateState (becomePreCandidateState s)).term = s.term + 1`. -/
theorem preCandidate_candidate_term (s : RaftState) :
    (becomeCandidateState (becomePreCandidateState s)).term = s.term + 1 := by
  simp [becomeCandidate_term, becomePreCandidate_term_unchanged]

/-- PROP-30  A node can reach `Leader` state from `Candidate` via
    `becomeLeaderState ∘ becomeCandidateState`. -/
theorem follower_to_leader_via_candidate (s : RaftState) :
    (becomeLeaderState (becomeCandidateState s)).state = .Leader := by
  simp [becomeLeader_state]

/-- PROP-31  The term is strictly higher after the full election cycle
    (Follower → Candidate → Leader) than it was at the start. -/
theorem election_cycle_term_increases (s : RaftState) :
    s.term < (becomeLeaderState (becomeCandidateState s)).term := by
  simp [becomeLeader_term_preserved, becomeCandidate_term]

/-! ## Decidable examples -/

-- A follower at term 1 becomes a candidate at term 2, self-voting
#eval becomeCandidateState ⟨2, .Follower, 1, 0, 0⟩
-- { id := 2, state := Candidate, term := 2, vote := 2, leaderId := 0 }

-- The candidate wins and becomes leader; term unchanged, vote preserved
#eval becomeLeaderState ⟨2, .Candidate, 2, 2, 0⟩
-- { id := 2, state := Leader, term := 2, vote := 2, leaderId := 2 }

-- A leader steps down to follower at a new term; vote is cleared
#eval becomeFollowerState ⟨2, .Leader, 3, 2, 2⟩ 4 5
-- { id := 2, state := Follower, term := 4, vote := 0, leaderId := 5 }

-- Same-term demotion: vote is preserved
#eval becomeFollowerState ⟨2, .Leader, 3, 2, 2⟩ 3 0
-- { id := 2, state := Follower, term := 3, vote := 2, leaderId := 0 }

-- Pre-candidate: term and vote unchanged
#eval becomePreCandidateState ⟨2, .Follower, 1, 0, 0⟩
-- { id := 2, state := PreCandidate, term := 1, vote := 0, leaderId := 0 }

-- Pre-vote path: PreCandidate → Candidate increments term
#eval becomeCandidateState (becomePreCandidateState ⟨3, .Follower, 5, 0, 0⟩)
-- { id := 3, state := Candidate, term := 6, vote := 3, leaderId := 0 }

end FVSquad.StateTransitions
