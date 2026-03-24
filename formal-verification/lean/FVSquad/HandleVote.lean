/-!
# HandleVote — Lean 4 Specification and Implementation (Phase 3 + 4)

Models the `MsgRequestVote | MsgRequestPreVote` arm of `RaftCore::step()` in
`src/raft.rs` (lines ≈ 1485–1530).

## Relevant Rust code

```rust
MessageType::MsgRequestVote | MessageType::MsgRequestPreVote => {
    let can_vote = (self.vote == m.from)
        || (self.vote == INVALID_ID && self.leader_id == INVALID_ID)
        || (m.get_msg_type() == MessageType::MsgRequestPreVote && m.term > self.term);
    if can_vote
        && self.raft_log.is_up_to_date(m.index, m.log_term)
        && (m.index > self.raft_log.last_index() || self.priority <= get_priority(&m))
    {
        let mut to_send = new_message(m.from, vote_resp_msg_type, None);
        to_send.term = m.term;
        to_send.reject = false;
        if m.get_msg_type() == MessageType::MsgRequestVote {
            self.vote = m.from;
            self.election_elapsed = 0;
        }
        self.msgs.push(to_send);
    } else {
        let mut to_send = new_message(m.from, vote_resp_msg_type, None);
        to_send.term = self.term;
        to_send.reject = true;
        to_send.commit = self.raft_log.committed;
        // commit_term set...
        self.msgs.push(to_send);
        self.maybe_commit_by_vote(&m);
    }
}
```

## Model scope and approximations

* `NodeId`, `Term`, log indices modelled as `Nat`.
* `Int` models Rust's `i64`; `Nat` models `u64`.
* `INVALID_ID = 0` (same convention as `FVSquad.VoteCommitment`).
* `get_priority` is abstracted: `VoteRequest.priority : Int` is the pre-computed
  result of `get_priority(&m)`.
* `maybe_commit_by_vote` is **omitted** — this file models only the vote response.
* The leader-lease early-return guard (before this arm) is **not modelled** —
  the handler is assumed to be reached unconditionally.
* I/O, message queuing, network, persistence are all omitted.
* Log contents are abstracted to `(last_log_term, last_log_index)`.
* The `check_quorum` flag and lease timing are not modelled.

See `FVSquad.VoteCommitment` for the simpler at-most-one-vote safety invariant;
this file extends that with the full three-condition decision and pre-vote semantics.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Tactic

namespace FVSquad.HandleVote

/-! ## Types -/

abbrev NodeId := Nat
abbrev Term   := Nat

/-- `INVALID_ID = 0` — same convention as Rust's `INVALID_ID`. -/
def INVALID_ID : NodeId := 0

/-- A vote request received by this node. -/
structure VoteRequest where
  /-- Sending candidate ID. -/
  from_       : NodeId
  /-- Candidate's term. For pre-votes this may be `self.term + 1`. -/
  term        : Term
  /-- Candidate's last log index. -/
  log_index   : Nat
  /-- Candidate's last log term. -/
  log_term    : Term
  /-- Effective priority of the candidate (result of `get_priority(&m)`). -/
  priority    : Int
  /-- `true` iff this is a `MsgRequestPreVote` (dry-run). -/
  is_pre_vote : Bool
  deriving Repr, DecidableEq

/-- The voter's local state (fields relevant to vote handling). -/
structure VoterState where
  /-- Current term. -/
  term              : Term
  /-- Candidate voted for in this term (`INVALID_ID` = not yet voted). -/
  vote              : NodeId
  /-- Known leader ID (`INVALID_ID` = no current leader). -/
  leader_id         : NodeId
  /-- Ticks since last election activity. -/
  election_elapsed  : Nat
  /-- Voter's last log term (abstraction of `raft_log.last_term()`). -/
  last_log_term     : Term
  /-- Voter's last log index (abstraction of `raft_log.last_index()`). -/
  last_log_index    : Nat
  /-- Voter's election priority. -/
  priority          : Int
  deriving Repr, DecidableEq

/-- The response fields emitted by the handler.
    (Commit hint fields from the reject path are not modelled.) -/
structure VoteResponse where
  /-- `true` = rejected, `false` = granted. -/
  reject    : Bool
  /-- Term echoed back: `req.term` on grant, `s.term` on reject. -/
  resp_term : Term
  deriving Repr, DecidableEq

/-- Combined output: updated voter state + response fields. -/
structure HandleVoteResult where
  new_state : VoterState
  response  : VoteResponse
  deriving Repr, DecidableEq

/-! ## Implementation model -/

/-- `canVote`: three-clause willingness predicate.

    Clause 1 (repeat): node already voted for this candidate.
    Clause 2 (first):  node hasn't voted yet AND sees no current leader.
    Clause 3 (pre-vote): this is a pre-vote for a strictly future term. -/
def canVote (s : VoterState) (req : VoteRequest) : Bool :=
  (s.vote == req.from_)
  || (s.vote == INVALID_ID && s.leader_id == INVALID_ID)
  || (req.is_pre_vote && req.term > s.term)

/-- `isUpToDate`: the candidate's log must dominate the voter's log.
    Term comparison takes priority; index is the tie-breaker. -/
def isUpToDate (s : VoterState) (req : VoteRequest) : Bool :=
  (req.log_term > s.last_log_term)
  || (req.log_term == s.last_log_term && req.log_index >= s.last_log_index)

/-- `priorityOk`: vote is permitted from a priority standpoint.
    Allowed if the candidate is strictly ahead in the log, or if the candidate's
    priority is at least as high as the voter's priority. -/
def priorityOk (s : VoterState) (req : VoteRequest) : Bool :=
  (req.log_index > s.last_log_index) || (s.priority <= req.priority)

/-- `shouldGrant`: all three conditions must hold. -/
def shouldGrant (s : VoterState) (req : VoteRequest) : Bool :=
  canVote s req && isUpToDate s req && priorityOk s req

/-- `handleVote`: pure model of the vote handler.

    Grant path (`shouldGrant = true`):
    * Response: `reject = false`, `resp_term = req.term`.
    * For a real vote: record `vote := req.from_` and reset `election_elapsed := 0`.
    * For a pre-vote: state is unchanged.

    Reject path:
    * Response: `reject = true`, `resp_term = s.term`.
    * State is unchanged (`maybe_commit_by_vote` is omitted). -/
def handleVote (s : VoterState) (req : VoteRequest) : HandleVoteResult :=
  if shouldGrant s req then
    let new_state :=
      if req.is_pre_vote then s
      else { s with vote := req.from_, election_elapsed := 0 }
    { new_state := new_state,
      response  := { reject := false, resp_term := req.term } }
  else
    { new_state := s,
      response  := { reject := true, resp_term := s.term } }

/-! ## Helper lemmas -/

private lemma shouldGrant_true_iff (s : VoterState) (req : VoteRequest) :
    shouldGrant s req = true ↔
    canVote s req = true ∧ isUpToDate s req = true ∧ priorityOk s req = true := by
  simp [shouldGrant, Bool.and_eq_true]

private lemma shouldGrant_false_of_canVote_false {s : VoterState} {req : VoteRequest}
    (h : canVote s req = false) : shouldGrant s req = false := by
  simp [shouldGrant, h]

/-! ## Propositions -/

/-- PROP-1 (**Pre-vote non-commitment**): handling a pre-vote never mutates
    `vote`, `term`, or `election_elapsed`. -/
theorem pre_vote_does_not_commit (s : VoterState) (req : VoteRequest)
    (hpre : req.is_pre_vote = true) :
    let r := handleVote s req
    r.new_state.vote = s.vote
    ∧ r.new_state.term = s.term
    ∧ r.new_state.election_elapsed = s.election_elapsed := by
  simp only [handleVote]
  split_ifs with hg
  · simp [hpre]
  · simp

/-- PROP-2 (**Response term on grant**): if the vote is granted, the response
    term equals `req.term`. -/
theorem vote_response_term_grant (s : VoterState) (req : VoteRequest)
    (hgrant : (handleVote s req).response.reject = false) :
    (handleVote s req).response.resp_term = req.term := by
  simp only [handleVote] at *
  split_ifs at * <;> simp_all

/-- PROP-3 (**Response term on reject**): if the vote is rejected, the response
    term equals the voter's own term. -/
theorem vote_response_term_reject (s : VoterState) (req : VoteRequest)
    (hrej : (handleVote s req).response.reject = true) :
    (handleVote s req).response.resp_term = s.term := by
  simp only [handleVote] at *
  split_ifs at * <;> simp_all

/-- PROP-4 (**Grant implies `canVote`**): a vote is granted only if `canVote`
    holds. -/
theorem grant_implies_canVote (s : VoterState) (req : VoteRequest)
    (hgrant : (handleVote s req).response.reject = false) :
    canVote s req = true := by
  simp only [handleVote] at hgrant
  split_ifs with hg at hgrant
  · exact ((shouldGrant_true_iff s req).mp hg).1
  · simp at hgrant

/-- PROP-5 (**Grant implies up-to-date**): a vote is granted only if
    `isUpToDate` holds. -/
theorem grant_implies_upToDate (s : VoterState) (req : VoteRequest)
    (hgrant : (handleVote s req).response.reject = false) :
    isUpToDate s req = true := by
  simp only [handleVote] at hgrant
  split_ifs with hg at hgrant
  · exact ((shouldGrant_true_iff s req).mp hg).2.1
  · simp at hgrant

/-- PROP-6 (**Grant implies priorityOk**): a vote is granted only if
    `priorityOk` holds. -/
theorem grant_implies_priorityOk (s : VoterState) (req : VoteRequest)
    (hgrant : (handleVote s req).response.reject = false) :
    priorityOk s req = true := by
  simp only [handleVote] at hgrant
  split_ifs with hg at hgrant
  · exact ((shouldGrant_true_iff s req).mp hg).2.2
  · simp at hgrant

/-- PROP-7 (**Real grant resets election timer**): if a real (non-pre-vote) is
    granted, `election_elapsed` is set to 0. -/
theorem real_grant_resets_timer (s : VoterState) (req : VoteRequest)
    (hgrant : (handleVote s req).response.reject = false)
    (hreal  : req.is_pre_vote = false) :
    (handleVote s req).new_state.election_elapsed = 0 := by
  simp only [handleVote] at *
  split_ifs at * <;> simp_all

/-- PROP-8 (**Vote recorded on real grant**): after a real-vote grant, the
    voter's `vote` field records `req.from_`. -/
theorem real_grant_records_vote (s : VoterState) (req : VoteRequest)
    (hgrant : (handleVote s req).response.reject = false)
    (hreal  : req.is_pre_vote = false) :
    (handleVote s req).new_state.vote = req.from_ := by
  simp only [handleVote] at *
  split_ifs at * <;> simp_all

/-- PROP-9 (**Reject leaves state unchanged**): when the vote is rejected,
    the voter state is not mutated. -/
theorem reject_leaves_state_unchanged (s : VoterState) (req : VoteRequest)
    (hrej : (handleVote s req).response.reject = true) :
    (handleVote s req).new_state = s := by
  simp only [handleVote] at *
  split_ifs at * <;> simp_all

/-- PROP-10 (**At most one vote per term — core safety invariant**):
    if the node has already voted for a *different* candidate (`vote ≠ INVALID_ID`
    and `vote ≠ req.from_`) and this is a real vote (not pre-vote), then the
    request is rejected.

    This is the fundamental Raft election safety property: no node can grant real
    votes to two distinct candidates in the same term. -/
theorem at_most_one_vote (s : VoterState) (req : VoteRequest)
    (hvoted : s.vote ≠ INVALID_ID) (hdiff : s.vote ≠ req.from_)
    (hnopre : req.is_pre_vote = false) :
    (handleVote s req).response.reject = true := by
  simp only [handleVote]
  have hcv : canVote s req = false := by
    simp only [canVote, INVALID_ID, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
               hnopre, Bool.false_and, Bool.false_eq_true, false_and, false_or]
    push_neg
    exact ⟨hdiff, Or.inl hvoted⟩
  simp [shouldGrant_false_of_canVote_false hcv]

/-- PROP-11 (**`isUpToDate` — term dominates**): if the candidate's log term is
    strictly greater, `isUpToDate` holds regardless of index. -/
theorem upToDate_term_dominates (s : VoterState) (req : VoteRequest)
    (h : req.log_term > s.last_log_term) :
    isUpToDate s req = true := by
  simp [isUpToDate, h]

/-- PROP-12 (**`isUpToDate` — same term, at least as long**): equal log terms
    with a non-shorter index also satisfies `isUpToDate`. -/
theorem upToDate_same_term_ge (s : VoterState) (req : VoteRequest)
    (ht : req.log_term = s.last_log_term) (hi : req.log_index ≥ s.last_log_index) :
    isUpToDate s req = true := by
  simp [isUpToDate, ht, hi]

/-- PROP-13 (**`isUpToDate` is false when log term is behind**): if the
    candidate's log term is strictly less than the voter's, the check fails. -/
theorem not_upToDate_term_behind (s : VoterState) (req : VoteRequest)
    (h : req.log_term < s.last_log_term) :
    isUpToDate s req = false := by
  simp only [isUpToDate, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
             Bool.not_eq_true, decide_eq_false_iff_not, beq_eq_false_iff_ne,
             gt_iff_lt, ge_iff_le, not_le]
  omega

/-- PROP-14 (**`priorityOk` when candidate is ahead in log**): if the
    candidate's last index is strictly greater than the voter's, priority is
    irrelevant. -/
theorem priorityOk_when_ahead (s : VoterState) (req : VoteRequest)
    (h : req.log_index > s.last_log_index) :
    priorityOk s req = true := by
  simp [priorityOk, h]

/-- PROP-15 (**`canVote` — repeat vote**): if the node already voted for this
    exact candidate, `canVote` is true. -/
theorem canVote_repeat (s : VoterState) (req : VoteRequest)
    (h : s.vote = req.from_) :
    canVote s req = true := by
  simp [canVote, h]

/-- PROP-16 (**`canVote` — first vote, no leader**): if the node hasn't voted
    and sees no current leader, `canVote` is true. -/
theorem canVote_first_vote_no_leader (s : VoterState) (req : VoteRequest)
    (hv : s.vote = INVALID_ID) (hl : s.leader_id = INVALID_ID) :
    canVote s req = true := by
  simp [canVote, INVALID_ID, hv, hl]

/-- PROP-17 (**`canVote` — pre-vote for future term**): a pre-vote for a
    strictly later term always passes `canVote` regardless of the local vote and
    leader state. -/
theorem canVote_preVote_future_term (s : VoterState) (req : VoteRequest)
    (hpre : req.is_pre_vote = true) (hterm : req.term > s.term) :
    canVote s req = true := by
  simp [canVote, hpre, hterm]

/-- PROP-18 (**`priorityOk` — voter's priority is not higher than candidate's**):
    if the voter's priority is ≤ candidate's priority, `priorityOk` is true even
    when log indexes are tied. -/
theorem priorityOk_equal_priority (s : VoterState) (req : VoteRequest)
    (h : s.priority ≤ req.priority) :
    priorityOk s req = true := by
  simp [priorityOk, h]

/-- PROP-19 (**Lower-priority candidate, tied log → reject**): if the voter has
    strictly higher priority than the candidate and both have the same last index,
    the candidate cannot win the vote on priority grounds. -/
theorem reject_lower_priority_tied_log (s : VoterState) (req : VoteRequest)
    (hv : s.vote = INVALID_ID) (hl : s.leader_id = INVALID_ID)
    (hprio : s.priority > req.priority)
    (htied : req.log_index = s.last_log_index)
    (hterm : req.log_term = s.last_log_term)
    (hnopre : req.is_pre_vote = false) :
    (handleVote s req).response.reject = true := by
  simp only [handleVote]
  have hpo : priorityOk s req = false := by
    simp only [priorityOk, Bool.or_eq_false_iff, Bool.not_eq_true,
               decide_eq_false_iff_not, gt_iff_lt, not_le]
    exact ⟨by omega, by linarith⟩
  have hsg : shouldGrant s req = false := by
    simp [shouldGrant, Bool.and_eq_false_iff, hpo]
  simp [hsg]

/-! ## Decidable examples (sanity checks) -/

-- Normal first vote: no prior vote, no leader, equal log → grant
#eval handleVote
  { term := 1, vote := 0, leader_id := 0, election_elapsed := 5,
    last_log_term := 1, last_log_index := 3, priority := 0 }
  { from_ := 2, term := 1, log_index := 3, log_term := 1,
    priority := 0, is_pre_vote := false }
-- Expect: reject = false, vote := 2, election_elapsed := 0

-- Different candidate same term → reject (already voted for 2)
#eval handleVote
  { term := 1, vote := 2, leader_id := 0, election_elapsed := 0,
    last_log_term := 1, last_log_index := 3, priority := 0 }
  { from_ := 3, term := 1, log_index := 3, log_term := 1,
    priority := 0, is_pre_vote := false }
-- Expect: reject = true

-- Repeat vote same candidate → grant
#eval handleVote
  { term := 1, vote := 2, leader_id := 0, election_elapsed := 0,
    last_log_term := 1, last_log_index := 3, priority := 0 }
  { from_ := 2, term := 1, log_index := 3, log_term := 1,
    priority := 0, is_pre_vote := false }
-- Expect: reject = false (idempotent re-vote)

-- Pre-vote: state unchanged even on grant
#eval handleVote
  { term := 1, vote := 0, leader_id := 0, election_elapsed := 5,
    last_log_term := 1, last_log_index := 3, priority := 0 }
  { from_ := 2, term := 2, log_index := 4, log_term := 1,
    priority := 0, is_pre_vote := true }
-- Expect: reject = false, vote still 0 (pre-vote doesn't commit)

-- Candidate behind in log term → reject
#eval handleVote
  { term := 1, vote := 0, leader_id := 0, election_elapsed := 5,
    last_log_term := 2, last_log_index := 5, priority := 0 }
  { from_ := 2, term := 2, log_index := 3, log_term := 1,
    priority := 0, is_pre_vote := false }
-- Expect: reject = true (log_term 1 < voter's 2)

-- High-priority voter, tied log index → reject lower-priority candidate
#eval handleVote
  { term := 1, vote := 0, leader_id := 0, election_elapsed := 5,
    last_log_term := 1, last_log_index := 3, priority := 5 }
  { from_ := 2, term := 1, log_index := 3, log_term := 1,
    priority := 3, is_pre_vote := false }
-- Expect: reject = true (voter priority 5 > candidate priority 3, same last_index)

-- Candidate strictly ahead → priority irrelevant
#eval handleVote
  { term := 1, vote := 0, leader_id := 0, election_elapsed := 5,
    last_log_term := 1, last_log_index := 3, priority := 5 }
  { from_ := 2, term := 1, log_index := 4, log_term := 1,
    priority := 1, is_pre_vote := false }
-- Expect: reject = false (candidate one entry ahead, priority_ok by log lead)

end FVSquad.HandleVote
