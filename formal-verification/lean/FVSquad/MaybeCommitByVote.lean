/-!
# MaybeCommitByVote — Lean 4 Specification, Implementation, and Proofs

Models `RaftCore::maybe_commit_by_vote` in `src/raft.rs` (lines ≈ 2219–2250):
a TiKV-specific fast-forward optimisation that advances a follower/candidate's
commit index upon receipt of a vote-rejection message.

## Relevant Rust code

```rust
fn maybe_commit_by_vote(&mut self, m: &Message) {
    if m.commit == 0 || m.commit_term == 0 {
        return;
    }
    let last_commit = self.raft_log.committed;
    if m.commit <= last_commit || self.state == StateRole::Leader {
        return;
    }
    if !self.raft_log.maybe_commit(m.commit, m.commit_term) {
        return;
    }
    // ... logging (omitted) ...
    if self.state != StateRole::Candidate && self.state != StateRole::PreCandidate {
        return;
    }
    let low  = last_commit + 1;
    let high = self.raft_log.committed + 1;
    let ctx  = GetEntriesContext(GetEntriesFor::CommitByVote);
    if self.has_unapplied_conf_changes(low, high, ctx) {
        let term = self.term;
        self.become_follower(term, INVALID_ID);
    }
}
```

## Model scope and approximations

* **`maybe_commit`** is abstracted as a Boolean predicate `canAdvance`:
  `canAdvance(log, commit_idx, commit_term)` holds when the local log has an
  entry at `commit_idx` with term `commit_term` AND `commit_idx > committed`.
  We do not model the log internals; only the Boolean outcome matters here.
* **`has_unapplied_conf_changes`** is abstracted as a Boolean parameter
  `hasConfChange : Bool` provided to the model.
* **`become_follower`** is modelled as setting `state := Follower`.
  We do NOT model the leader-id or heartbeat-elapsed fields it also sets.
* **Term** is modelled as a `Nat`; we verify it is unchanged by this function.
* **StateRole** has four values: Leader, Follower, Candidate, PreCandidate.
* I/O, logging, inflight windows, and progress tracking are omitted.

🔬 *Lean Squad — automated formal verification.*
-/

import Mathlib.Tactic

namespace FVSquad.MaybeCommitByVote

/-! ## Types -/

/-- Raft node state roles. -/
inductive StateRole where
  | Leader
  | Follower
  | Candidate
  | PreCandidate
  deriving DecidableEq, Repr

/-- Minimal Raft node state for this model. -/
structure RaftState where
  /-- Current term. -/
  term      : Nat
  /-- Node's current role. -/
  state     : StateRole
  /-- Current commit index. -/
  committed : Nat
  deriving Repr

/-- Incoming vote-response message fields relevant to `maybe_commit_by_vote`. -/
structure VoteMsg where
  /-- Voter's committed index (0 = not provided). -/
  commit      : Nat
  /-- Term of the entry at `commit` (0 = not provided). -/
  commit_term : Nat
  deriving Repr

/-! ## Implementation model -/

/-- `maybe_commit_by_vote` result.
    We separate the outcome from the abstract parameters to keep the model clean. -/
structure McbvResult where
  /-- Updated committed index. -/
  committed : Nat
  /-- Updated state. -/
  state     : StateRole
  /-- Updated term (should be unchanged). -/
  term      : Nat
  deriving Repr

/-- Pure model of `maybe_commit_by_vote`.
    Parameters:
    - `s`: node state before the call
    - `m`: the incoming vote-response message
    - `canAdvance`: abstract result of `raft_log.maybe_commit(m.commit, m.commit_term)`.
      Precondition: `canAdvance → m.commit > s.committed` (the log check subsumes this).
    - `hasConfChange`: abstract result of `has_unapplied_conf_changes(low, high, ctx)`.
-/
def maybeCommitByVote
    (s            : RaftState)
    (m            : VoteMsg)
    (canAdvance   : Bool)     -- abstract: log has m.commit with m.commit_term
    (hasConfChange : Bool)    -- abstract: conf change in (last_commit, m.commit]
    : McbvResult :=
  -- Guard 1: invalid commit fields
  if m.commit = 0 ∨ m.commit_term = 0 then
    ⟨s.committed, s.state, s.term⟩
  else
  -- Guard 2: already committed or is leader
  if m.commit ≤ s.committed ∨ s.state = StateRole.Leader then
    ⟨s.committed, s.state, s.term⟩
  else
  -- Guard 3: log check (maybe_commit)
  if ¬canAdvance then
    ⟨s.committed, s.state, s.term⟩
  else
    -- Commit is advanced to m.commit
    let new_committed := m.commit
    -- Check if we need to step down (Candidate / PreCandidate + conf change)
    let new_state :=
      if (s.state = StateRole.Candidate ∨ s.state = StateRole.PreCandidate) ∧ hasConfChange then
        StateRole.Follower
      else
        s.state
    ⟨new_committed, new_state, s.term⟩

/-! ## Helper: noop check -/

/-- `maybeCommitByVote` returns the original committed index and state (a no-op). -/
def isNoop (s : RaftState) (r : McbvResult) : Prop :=
  r.committed = s.committed ∧ r.state = s.state

/-! ## Theorems -/

/-- **P1** `invalid_fields_noop`: zero commit or commit_term → no change. -/
theorem p1_invalid_fields_noop
    (s : RaftState) (m : VoteMsg)
    (ca : Bool) (hcc : Bool)
    (h : m.commit = 0 ∨ m.commit_term = 0) :
    let r := maybeCommitByVote s m ca hcc
    r.committed = s.committed ∧ r.state = s.state ∧ r.term = s.term := by
  simp [maybeCommitByVote]
  rcases h with h | h <;> simp [h]

/-- **P2** `already_committed_noop`: `m.commit ≤ committed` → no change. -/
theorem p2_already_committed_noop
    (s : RaftState) (m : VoteMsg)
    (ca : Bool) (hcc : Bool)
    (hc : m.commit ≤ s.committed)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0) :
    let r := maybeCommitByVote s m ca hcc
    r.committed = s.committed ∧ r.state = s.state := by
  simp [maybeCommitByVote, hm, ht, hc]

/-- **P3** `leader_noop`: Leader state → no change. -/
theorem p3_leader_noop
    (s : RaftState) (m : VoteMsg)
    (ca : Bool) (hcc : Bool)
    (hs : s.state = StateRole.Leader)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0) :
    let r := maybeCommitByVote s m ca hcc
    r.committed = s.committed ∧ r.state = s.state := by
  simp [maybeCommitByVote, hm, ht, hs]

/-- **P4** `log_fail_noop`: `canAdvance = false` → no change. -/
theorem p4_log_fail_noop
    (s : RaftState) (m : VoteMsg) (hcc : Bool)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader)) :
    let r := maybeCommitByVote s m false hcc
    r.committed = s.committed ∧ r.state = s.state := by
  simp [maybeCommitByVote, hm, ht, hg]

/-- **P5** `commit_advances`: successful call advances committed to `m.commit`. -/
theorem p5_commit_advances
    (s : RaftState) (m : VoteMsg) (hcc : Bool)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader)) :
    (maybeCommitByVote s m true hcc).committed = m.commit := by
  simp [maybeCommitByVote, hm, ht, hg]

/-- **P6** `commit_monotone`: committed index never decreases. -/
theorem p6_commit_monotone
    (s : RaftState) (m : VoteMsg)
    (ca : Bool) (hcc : Bool) :
    (maybeCommitByVote s m ca hcc).committed ≥ s.committed := by
  simp only [maybeCommitByVote]
  split_ifs with h1 h2 h3 <;> simp_all
  -- Only the `canAdvance` branch can change committed; there m.commit > s.committed
  -- is guaranteed by guard 2's second disjunct failing.
  push_neg at h2
  omega

/-- **P7** `term_always_preserved`: term is never changed by this function. -/
theorem p7_term_preserved
    (s : RaftState) (m : VoteMsg)
    (ca : Bool) (hcc : Bool) :
    (maybeCommitByVote s m ca hcc).term = s.term := by
  simp [maybeCommitByVote]
  split_ifs <;> simp

/-- **P8** `candidate_stepdown_on_confchange`:
    A candidate (or pre-candidate) steps down to Follower when a conf change is
    among the newly committed entries. -/
theorem p8_candidate_stepdown_on_confchange
    (s : RaftState) (m : VoteMsg)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader))
    (hcand : s.state = StateRole.Candidate ∨ s.state = StateRole.PreCandidate) :
    (maybeCommitByVote s m true true).state = StateRole.Follower := by
  simp [maybeCommitByVote, hm, ht, hg, hcand]

/-- **P9** `candidate_stays_candidate_no_confchange`:
    If no conf change in the newly committed range, a candidate stays a candidate. -/
theorem p9_candidate_stays_candidate
    (s : RaftState) (m : VoteMsg)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader))
    (hcand : s.state = StateRole.Candidate) :
    (maybeCommitByVote s m true false).state = StateRole.Candidate := by
  simp [maybeCommitByVote, hm, ht, hg, hcand]

/-- **P10** `precand_stays_precand_no_confchange`:
    If no conf change, a pre-candidate stays a pre-candidate. -/
theorem p10_precand_stays_precand
    (s : RaftState) (m : VoteMsg)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader))
    (hpc : s.state = StateRole.PreCandidate) :
    (maybeCommitByVote s m true false).state = StateRole.PreCandidate := by
  simp [maybeCommitByVote, hm, ht, hg, hpc]

/-- **P11** `follower_stays_follower`:
    A Follower that advances the commit index remains a Follower. -/
theorem p11_follower_stays_follower
    (s : RaftState) (m : VoteMsg) (hcc : Bool)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader))
    (hf : s.state = StateRole.Follower) :
    (maybeCommitByVote s m true hcc).state = StateRole.Follower := by
  simp [maybeCommitByVote, hm, ht, hg, hf]

/-- **P12** `leader_excluded`:
    After the call, the state is never set to Leader by this function. -/
theorem p12_no_new_leader
    (s : RaftState) (m : VoteMsg)
    (ca : Bool) (hcc : Bool) :
    (maybeCommitByVote s m ca hcc).state = StateRole.Leader →
    s.state = StateRole.Leader := by
  simp only [maybeCommitByVote]
  split_ifs with h1 h2 h3 h4 <;> simp_all
  -- In the confchange branch: new_state = Follower ≠ Leader
  split_ifs at * <;> simp_all

/-- **P13** `idempotent_second_call`:
    A second call with the same message is a no-op (already committed). -/
theorem p13_idempotent
    (s : RaftState) (m : VoteMsg)
    (hcc : Bool) (hcc2 : Bool)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader))
    (ha : (maybeCommitByVote s m true hcc).committed = m.commit) :
    let s' : RaftState :=
      { state     := (maybeCommitByVote s m true hcc).state
        committed := (maybeCommitByVote s m true hcc).committed
        term      := (maybeCommitByVote s m true hcc).term }
    (maybeCommitByVote s' m true hcc2).committed = m.commit ∧
    (maybeCommitByVote s' m true hcc2).state = s'.state := by
  simp [maybeCommitByVote, hm, ht, hg, ha]

/-- **P14** `commit_value_when_advanced`:
    When commit advances, the new value equals `m.commit`. -/
theorem p14_commit_exact_value
    (s : RaftState) (m : VoteMsg) (hcc : Bool)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader)) :
    (maybeCommitByVote s m true hcc).committed = m.commit := by
  simp [maybeCommitByVote, hm, ht, hg]

/-- **P15** `stepdown_term_unchanged`:
    When a candidate steps down, the term remains the same. -/
theorem p15_stepdown_term_unchanged
    (s : RaftState) (m : VoteMsg)
    (hm : m.commit ≠ 0) (ht : m.commit_term ≠ 0)
    (hg : ¬(m.commit ≤ s.committed ∨ s.state = StateRole.Leader))
    (hcand : s.state = StateRole.Candidate) :
    (maybeCommitByVote s m true true).term = s.term := by
  simp [maybeCommitByVote, hm, ht, hg, hcand]

end FVSquad.MaybeCommitByVote
