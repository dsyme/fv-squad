/-!
# Vote Commitment — Lean 4 Specification and Implementation

Models the Raft safety invariant: **a node casts at most one real vote per term**.

Relevant Rust logic in `src/raft.rs`:

```rust
// In step() for MsgRequestVote (simplified):
let can_vote = (self.vote == m.from)           // repeat for same candidate
            || (self.vote == INVALID_ID         // haven't voted yet
                && self.leader_id == INVALID_ID);
if can_vote && log_up_to_date && priority_ok {
    self.vote = m.from;                         // record real vote
}

// In reset(term):
if self.term != term {
    self.term = term;
    self.vote = INVALID_ID;                     // clear vote on term change
}

// In become_candidate():
let term = self.term + 1;
self.reset(term);        // clears vote (new term)
self.vote = id;          // node votes for itself
```

## Key safety invariant

At most one real vote is cast per term: if `vote ≠ INVALID_ID`, then `can_vote`
succeeds only for the candidate already recorded (repeat-vote branch).

## Model scope and approximations

* `NodeId` modelled as `Nat` (Rust `u64`; 64-bit bound not modelled).
* `Term` modelled as `Nat`.
* `INVALID_ID = 0` (no real node has this ID).
* `leader_id` check in `can_vote` is **omitted**: our model is more permissive,
  making safety properties stronger (they hold in a more generous setting).
* Pre-vote requests (which do **not** update `self.vote`) are out of scope.
* Log up-to-date check and priority check are abstracted away.
* I/O, messaging, and persistence are omitted.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Tactic

namespace FVSquad.VoteCommitment

/-! ## Types and constants -/

abbrev NodeId := Nat
abbrev Term   := Nat

/-- Node ID 0 represents "no vote cast" (`INVALID_ID = 0` in Rust). -/
def INVALID_ID : NodeId := 0

/-- The vote-relevant portion of a Raft node's state. -/
structure VoteState where
  term : Term
  /-- 0 = `INVALID_ID` (no vote cast this term). -/
  vote : NodeId
  deriving Repr, DecidableEq

/-- A vote request (simplified: only the candidate id and term). -/
structure VoteReq where
  /-- The candidate requesting the vote. -/
  from_ : NodeId
  term  : Term
  deriving Repr, DecidableEq

/-! ## Implementation model -/

/-- `canVote`: a node can cast a real vote if:
    (1) it already voted for this candidate (repeat), or
    (2) it has not voted yet (`vote = INVALID_ID`).
    (Pre-vote case omitted — see approximations above.) -/
def canVote (s : VoteState) (req : VoteReq) : Bool :=
  s.vote == req.from_ || s.vote == INVALID_ID

/-- `grantVote`: record a real vote for `req.from_`. -/
def grantVote (s : VoteState) (req : VoteReq) : VoteState :=
  { s with vote := req.from_ }

/-- `resetTerm`: update term and clear the vote when the term advances (mirrors
    `RaftCore::reset`).  When the term is unchanged, the state is preserved. -/
def resetTerm (s : VoteState) (t : Term) : VoteState :=
  if s.term ≠ t then { term := t, vote := INVALID_ID }
  else s

/-- `becomeCandidateVote`: node increments term (clearing the old vote), then
    votes for itself — mirrors `become_candidate`. -/
def becomeCandidateVote (s : VoteState) (id : NodeId) : VoteState :=
  let s' := resetTerm s (s.term + 1)
  { s' with vote := id }

/-! ## Helper lemmas -/

private lemma resetTerm_of_ne {s : VoteState} {t : Term} (h : s.term ≠ t) :
    resetTerm s t = { term := t, vote := INVALID_ID } := by
  simp [resetTerm, h]

private lemma resetTerm_of_eq {s : VoteState} :
    resetTerm s s.term = s := by
  simp [resetTerm]

/-- `s.term + 1 ≠ s.term` always holds for `Nat`. -/
private lemma succ_ne_self (n : Nat) : n + 1 ≠ n := Nat.succ_ne_self n

/-- `becomeCandidateVote` always takes the new-term branch of `resetTerm`. -/
private lemma becomeCandidateVote_eq (s : VoteState) (id : NodeId) :
    becomeCandidateVote s id = { term := s.term + 1, vote := id } := by
  simp [becomeCandidateVote, resetTerm_of_ne (succ_ne_self s.term)]

/-! ## Propositions -/

/-- PROP-1  When the vote is `INVALID_ID` (no prior vote), `canVote` is true for
    any candidate. -/
theorem canVote_when_no_vote (s : VoteState) (req : VoteReq)
    (h : s.vote = INVALID_ID) : canVote s req = true := by
  simp [canVote, INVALID_ID, h]

/-- PROP-2  Repeat vote: `canVote` is true when the node already voted for this
    exact candidate. -/
theorem canVote_repeat (s : VoteState) (req : VoteReq)
    (h : s.vote = req.from_) : canVote s req = true := by
  simp [canVote, h]

/-- PROP-3  `canVote` is false if the node already voted for a *different*
    candidate — the node has committed its vote for this term. -/
theorem canVote_false_different_candidate (s : VoteState) (req : VoteReq)
    (hvoted : s.vote ≠ INVALID_ID) (hdiff : s.vote ≠ req.from_) :
    canVote s req = false := by
  simp only [canVote, INVALID_ID, Bool.or_eq_true, beq_iff_eq]
  push_neg
  exact ⟨hdiff, hvoted⟩

/-- PROP-4 (**Core safety — vote commitment**): At most one candidate is granted
    a vote per term.

    If a node has already voted (`vote ≠ INVALID_ID`), then `canVote` can only
    succeed for the same candidate that was recorded.  In other words, if two
    requests both pass `canVote`, they must be from the same candidate. -/
theorem vote_commitment (s : VoteState) (r1 r2 : VoteReq)
    (hv1 : canVote s r1 = true) (hv2 : canVote s r2 = true)
    (hvoted : s.vote ≠ INVALID_ID) :
    r1.from_ = r2.from_ := by
  simp only [canVote, INVALID_ID, Bool.or_eq_true, beq_iff_eq] at hv1 hv2
  rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
  · exact h1.symm.trans h2
  · exact absurd h2 hvoted
  · exact absurd h1 hvoted
  · exact absurd h1 hvoted

/-- PROP-5  `resetTerm` clears the vote when the term changes. -/
theorem resetTerm_clears_vote {s : VoteState} {t : Term} (h : s.term ≠ t) :
    (resetTerm s t).vote = INVALID_ID := by
  simp [resetTerm_of_ne h, INVALID_ID]

/-- PROP-6  `resetTerm` preserves the full state when the term is unchanged. -/
theorem resetTerm_same_term (s : VoteState) :
    resetTerm s s.term = s := resetTerm_of_eq

/-- PROP-7  After `resetTerm` to a new term, `canVote` is true for any candidate
    (the slate is clean). -/
theorem canVote_after_reset {s : VoteState} {t : Term} (h : s.term ≠ t)
    (req : VoteReq) : canVote (resetTerm s t) req = true := by
  simp [resetTerm_of_ne h, canVote, INVALID_ID]

/-- PROP-8  `grantVote` records the chosen candidate in the vote field. -/
theorem grantVote_records (s : VoteState) (req : VoteReq) :
    (grantVote s req).vote = req.from_ := by
  simp [grantVote]

/-- PROP-9  `grantVote` does not alter the term. -/
theorem grantVote_preserves_term (s : VoteState) (req : VoteReq) :
    (grantVote s req).term = s.term := by
  simp [grantVote]

/-- PROP-10  A `grantVote` makes `canVote` succeed for the same candidate
    (idempotence: voting for X lets X vote again). -/
theorem grantVote_canVote_self (s : VoteState) (req : VoteReq) :
    canVote (grantVote s req) req = true := by
  simp [canVote, grantVote]

/-- PROP-11  After `grantVote req`, `canVote` returns false for any *different*
    candidate (provided `req.from_ ≠ INVALID_ID`). -/
theorem grantVote_blocks_other (s : VoteState) (req other : VoteReq)
    (hdiff : req.from_ ≠ other.from_) (hne : req.from_ ≠ INVALID_ID) :
    canVote (grantVote s req) other = false := by
  simp only [canVote, grantVote, INVALID_ID, Bool.or_eq_true, beq_iff_eq]
  push_neg
  exact ⟨hdiff, hne⟩

/-- PROP-12  After `becomeCandidateVote`, the node has voted for itself. -/
theorem becomeCandidateVote_votes_self (s : VoteState) (id : NodeId) :
    (becomeCandidateVote s id).vote = id := by
  simp [becomeCandidateVote_eq]

/-- PROP-13  `becomeCandidateVote` increments the term by exactly 1. -/
theorem becomeCandidateVote_increments_term (s : VoteState) (id : NodeId) :
    (becomeCandidateVote s id).term = s.term + 1 := by
  simp [becomeCandidateVote_eq]

/-- PROP-14  Term monotonicity at candidacy: `becomeCandidateVote` strictly
    increases the term. -/
theorem becomeCandidateVote_term_increases (s : VoteState) (id : NodeId) :
    s.term < (becomeCandidateVote s id).term := by
  simp [becomeCandidateVote_eq]

/-- PROP-15  `resetTerm` is idempotent: a second `resetTerm` to the same target
    term is a no-op. -/
theorem resetTerm_idempotent (s : VoteState) (t : Term) :
    resetTerm (resetTerm s t) t = resetTerm s t := by
  by_cases h : s.term = t
  · subst h; simp [resetTerm_of_eq]
  · rw [resetTerm_of_ne h]; exact resetTerm_of_eq

/-! ## Decidable examples -/

-- No vote yet → any candidate passes
#eval canVote ⟨1, 0⟩ ⟨5, 1⟩      -- true

-- Already voted for 5 → same candidate passes
#eval canVote ⟨1, 5⟩ ⟨5, 1⟩      -- true

-- Already voted for 5 → different candidate blocked
#eval canVote ⟨1, 5⟩ ⟨3, 1⟩      -- false

-- become_candidate: term 1 → 2, node 2 votes for itself
#eval becomeCandidateVote ⟨1, 0⟩ 2   -- { term := 2, vote := 2 }

-- resetTerm clears vote on term change
#eval resetTerm ⟨1, 5⟩ 2             -- { term := 2, vote := 0 }

-- resetTerm preserves state when term unchanged
#eval resetTerm ⟨1, 5⟩ 1             -- { term := 1, vote := 5 }

-- canVote after reset
#eval canVote (resetTerm ⟨3, 7⟩ 4) ⟨99, 4⟩   -- true (vote cleared)

end FVSquad.VoteCommitment
