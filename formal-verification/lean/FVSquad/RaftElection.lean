import FVSquad.HasQuorum
import FVSquad.IsUpToDate

/-!
# RaftElection — Election Model and Safety

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file formalises the Raft leader election mechanism (§5.2 of the Raft paper) and proves
the core **ElectionSafety** property: at most one leader can be elected per term.

## Background

In Raft, a candidate wins an election by receiving votes from a **majority quorum** of voters.
The key safety property is that at most one candidate can win in any given term — because any
two majority quorums must share at least one voter (the quorum intersection property, HQ20),
and a voter may vote for at most one candidate per term.

## This File Provides

1. **`NodeRole`** (`Follower` / `Candidate` / `Leader`) — the role of a Raft node.

2. **`NodeState`** — the election-relevant state of a single node: `currentTerm`,
   `votedFor`, and `role`.  Models the persistent state in `src/raft.rs` (fields `term`,
   `vote`, and `state`).

3. **`VoteRecord`** — a pure function `Nat → Nat → Option Nat` (term → voter → candidate)
   modelling votes cast.  Because it is a function, it is automatically **single-valued**:
   `record term voter` can only return one value per `(term, voter)` pair.  This directly
   formalises the Raft invariant (§5.2) that each node votes for at most one candidate
   per term.

4. **`wonInTerm`** — the election outcome predicate: a candidate wins when a majority quorum
   of voters has voted for it in the given term.

5. **`voteGranted`** — the Raft vote-granting condition (§5.4.1): a node grants a vote iff
   (a) it has not yet voted in this term or has already voted for this candidate, and (b) the
   candidate's log is at least as up-to-date as the voter's log (`isUpToDate` from
   `FVSquad.IsUpToDate`).

6. **ElectionSafety theorem (RE5)** — at most one candidate wins per term.  The proof
   is short: two winning quorums must share a voter (HQ20); that voter voted for both
   winners; since `VoteRecord` is a function, the two winners are equal.

## Connection to `RaftTrace`

The `RaftReachable.step` constructor in `RaftTrace.lean` has the hypothesis `hqc_preserved`,
which says quorum-certified entries are preserved by protocol transitions.  This is the
formal expression of **Leader Completeness** (Raft §5.4.1): an elected leader has all
quorum-certified entries.  Discharging `hqc_preserved` from concrete protocol steps
requires:

1. **ElectionSafety** (this file, RE5): at most one leader per term.
2. **Leader Completeness** (future `LeaderCompleteness.lean`): the elected leader's log
   is at least as up-to-date as every voter who voted for it (uses IU16 from
   `FVSquad.IsUpToDate`).

## Modelling Notes

- Terms are `Nat` (not `u64`); no overflow modelled — practical log sizes are far below 2⁶³.
- Node IDs are `Nat` (not `u64`).
- `votedFor : Option Nat` — `none` represents "not yet voted" (INVALID_ID = 0 in the Rust
  uses a sentinel; we use `Option` for clarity).
- Abstracted away: log entries, committed index, message queues, election timers, `prs`,
  heartbeat tracking, leadership transfer.

## Theorem Table

### Election outcome theorems (RE1–RE15)

| ID   | Name                                  | Status    | Description                                                  |
|------|---------------------------------------|-----------|--------------------------------------------------------------|
| RE1  | `wonInTerm_nil`                       | ✅ proved  | Empty voter list: any candidate trivially satisfies quorum   |
| RE2  | `wonInTerm_iff`                       | ✅ proved  | `wonInTerm` unfolds to `hasQuorum` of the vote-check fn      |
| RE3  | `voteRecord_single_valued`            | ✅ proved  | VoteRecord is single-valued: one vote per voter per term     |
| RE4  | `shared_voter_of_two_winners`         | ✅ proved  | Two winners → explicit shared voter (HQ20 application)       |
| RE5  | `electionSafety`                      | ✅ proved  | **At most one winner per term** (ElectionSafety, §5.2)       |
| RE6  | `electionSafety_ne`                   | ✅ proved  | Contrapositive: c1 ≠ c2 → cannot both win                    |
| RE7  | `voteGranted_isUpToDate`              | ✅ proved  | Vote granted → candidate log is up-to-date                   |
| RE8  | `voteGranted_priorVote_none_or_self`  | ✅ proved  | Vote granted → prior vote is none or same candidate          |
| RE9  | `not_voteGranted_of_other_prior`      | ✅ proved  | Voted for c1 ≠ c2 → won't grant vote to c2                   |
| RE10 | `voteGranted_and_prior_eq`            | ✅ proved  | If granted vote and prior vote is set, prior = candidate     |
| RE11 | `wonInTerm_implies_some_voter`        | ✅ proved  | Nonempty voters + winner → ∃ voter who voted                 |
| RE12 | `wonInTerm_singleton_iff`             | ✅ proved  | Singleton cluster: wins iff sole voter voted                 |
| RE13 | `wonInTerm_singleton_self`            | ✅ proved  | Candidate voting for itself wins in singleton cluster        |
| RE14 | `electionSafety_two_leaders`         | ✅ proved  | Two nodes that won elections in same term → same ID          |
| RE15 | `wonInTerm_voter_voted`               | ✅ proved  | Every shared voter voted for the actual winner               |

### State transition theorems (RT1–RT15)

| ID   | Name                                   | Status    | Description |
|------|----------------------------------------|-----------|-------------|
| RT1  | `RT1_becomeFollower_term`              | ✅ proved  | Term after becomeFollower equals the given term |
| RT2  | `RT2_becomeFollower_role`              | ✅ proved  | Role is Follower after becomeFollower |
| RT3  | `RT3_becomeFollower_vote_reset`        | ✅ proved  | Vote cleared when term strictly increases |
| RT4  | `RT4_becomeFollower_vote_preserved`    | ✅ proved  | Vote preserved when term stays the same |
| RT5  | `RT5_becomeFollower_term_monotone`     | ✅ proved  | becomeFollower never decreases the term |
| RT6  | `RT6_becomeCandidate_term`             | ✅ proved  | Term after becomeCandidate = old term + 1 |
| RT7  | `RT7_becomeCandidate_role`             | ✅ proved  | Role is Candidate after becomeCandidate |
| RT8  | `RT8_becomeCandidate_vote`             | ✅ proved  | Candidate votes for itself |
| RT9  | `RT9_becomeCandidate_term_strict`      | ✅ proved  | becomeCandidate strictly increases the term |
| RT10 | `RT10_becomeLeader_role`               | ✅ proved  | Role is Leader after becomeLeader |
| RT11 | `RT11_becomeLeader_term_unchanged`     | ✅ proved  | Term is unchanged by becomeLeader |
| RT12 | `RT12_becomeLeader_vote_unchanged`     | ✅ proved  | Vote is unchanged by becomeLeader |
| RT13 | `RT13_becomeLeader_voted_for_self`     | ✅ proved  | After becomeCandidate+becomeLeader, leader voted for itself (I4) |
| RT14 | `RT14_becomeFollower_same_term_preserves_vote` | ✅ proved | Same-term becomeFollower preserves vote |
| RT15 | `RT15_term_monotone_sequence`          | ✅ proved  | Term monotonicity: both transitions only increase term |

### processVoteRequest and invariant theorems (RI1–RI15)

| ID   | Name                                          | Status    | Description |
|------|-----------------------------------------------|-----------|-------------|
| RI1  | `RI1_processVoteRequest_grants_vote`              | ✅ proved  | Vote granted when conditions met |
| RI2  | `RI2_processVoteRequest_denies_other_vote`        | ✅ proved  | Vote denied when already voted for different candidate |
| RI3  | `RI3_processVoteRequest_idempotent`               | ✅ proved  | Re-voting for same candidate is idempotent |
| RI4  | `RI4_processVoteRequest_term_nondecreasing`       | ✅ proved  | Term never decreases after processing vote request |
| RI5  | `RI5_processVoteRequest_higher_term_clears_vote`  | ✅ proved  | Higher-term request clears prior vote before checking |
| RI6  | `RI6_double_becomeCandidate_term`                 | ✅ proved  | Two consecutive becomeCandidate calls increment term by 2 |
| RI7  | `RI7_becomeCandidate_after_becomeFollower_term`   | ✅ proved  | becomeCandidate after becomeFollower(t) gives term t+1 |
| RI8  | `RI8_becomeFollower_idempotent_on_term`           | ✅ proved  | becomeFollower twice with same term: term unchanged |
| RI9  | `RI9_becomeFollower_chain_term`                   | ✅ proved  | becomeFollower(t1) then becomeFollower(t2): term = t2 |
| RI10 | `RI10_becomeLeader_after_sequence_term`            | ✅ proved  | becomeLeader ∘ becomeCandidate ∘ becomeFollower term arithmetic |
| RI11 | `RI11_leader_voted_self_via_candidate`             | ✅ proved  | I4: any leader reached via becomeCandidate voted for itself |
| RI12 | `RI12_candidate_term_gt_follower_term`             | ✅ proved  | Candidate always has a strictly higher term than preceding follower |
| RI13 | `RI13_wonInTerm_consistent_with_vote_record`       | ✅ proved  | VoteRecord consistency → winner uniqueness |
| RI14 | `RI14_processVoteRequest_voted_for_is_cand`        | ✅ proved  | After granting vote, votedFor = some candId |
| RI15 | `RI15_two_leaders_same_term_same_id`               | ✅ proved  | Two election winners in the same term are the same node |

### voteGranted characterisation and processVoteRequest structure (RV1–RV8)

| ID   | Name                                           | Status    | Description |
|------|------------------------------------------------|-----------|-------------|
| RV1  | `RV1_voteGranted_true_iff`                     | ✅ proved  | Biconditional: voteGranted = true ↔ prior-ok ∧ isUpToDate |
| RV2  | `RV2_voteGranted_false_of_not_upToDate`        | ✅ proved  | ¬isUpToDate → voteGranted = false |
| RV3  | `RV3_voteGranted_true_of_none_and_upToDate`    | ✅ proved  | prior=none ∧ isUpToDate → voteGranted = true |
| RV4  | `RV4_processVoteRequest_currentTerm`           | ✅ proved  | Resulting term = max(s.currentTerm, candTerm) |
| RV5  | `RV5_processVoteRequest_role_unchanged_low_term` | ✅ proved | ¬(candTerm > currentTerm) → role unchanged |
| RV6  | `RV6_processVoteRequest_higher_term_granted_state` | ✅ proved | Higher term + granted → full resulting state |
| RV7  | `RV7_processVoteRequest_higher_term_denied_state`  | ✅ proved | Higher term + denied → becomeFollower state  |
| RV8  | `RV8_wonInTerm_of_all_voters_voted`            | ✅ proved  | All voters voted → wonInTerm = true |
-/

namespace FVSquad.RaftElection

/-! ## Node roles -/

/-- The role of a Raft node.  Mirrors `StateRole` in `src/raft.rs:63–73`. -/
inductive NodeRole where
  | Follower  : NodeRole
  | Candidate : NodeRole
  | Leader    : NodeRole
  deriving DecidableEq, Repr

/-! ## Node state -/

/-- The election-relevant state of a single Raft node.

    Models the persistent state fields in `src/raft.rs:163–188`:
    - `term : u64` → `currentTerm : Nat` (no overflow)
    - `vote : u64` (0 = INVALID_ID) → `votedFor : Option Nat`
    - `state : StateRole` → `role : NodeRole`

    **Abstracted away**: log entries, `election_elapsed`, `leader_id`, `prs` (progress
    tracker), commit index, message queues, timers, randomised election timeout. -/
structure NodeState where
  /-- Latest term this node has seen (§5.1: increases monotonically). -/
  currentTerm : Nat
  /-- Candidate this node voted for in currentTerm; `none` if not yet voted (§5.2). -/
  votedFor    : Option Nat
  /-- Current role of the node. -/
  role        : NodeRole
  deriving DecidableEq, Repr

/-! ## Vote records -/

/-- A **VoteRecord** captures the votes cast across all terms:
    `record term voter` = `some c` if voter `voter` voted for candidate `c` in `term`,
    or `none` if voter `voter` has not yet voted in `term`.

    **Key design choice**: `VoteRecord` is a plain Lean function `Nat → Nat → Option Nat`.
    This means it is automatically **single-valued**: for any `(term, voter)` pair, the
    function can return at most one value.  This directly models the Raft §5.2 invariant
    that each node votes for at most one candidate per term, without needing an explicit
    axiom.  See `voteRecord_single_valued` (RE3). -/
abbrev VoteRecord := Nat → Nat → Option Nat

/-! ## Election outcome -/

/-- `wonInTerm voters record term candidate`: candidate `candidate` won the election
    in `term` — a majority quorum of `voters` voted for `candidate` in `term`.

    The vote-check function is `fun voter => decide (record term voter = some candidate)`,
    which returns `true` for exactly those voters whose record shows a vote for `candidate`.
    `hasQuorum` (from `FVSquad.HasQuorum`) checks whether this set forms a majority quorum.

    Mirrors the Rust `poll` function (`src/raft.rs:2259`), which tallies votes and
    declares victory when `tally_votes` returns `VoteResult::Won`. -/
def wonInTerm (voters : List Nat) (record : VoteRecord) (term candidate : Nat) : Bool :=
  hasQuorum voters (fun voter => decide (record term voter = some candidate))

/-! ## Vote-granting condition -/

/-- `voteGranted voterLog priorVote candId candLastTerm candLastIndex`: `true` iff the
    voter would grant a vote to candidate `candId`.

    The two conditions (Raft §5.2 and §5.4.1):
    1. **Prior-vote condition**: the voter has not yet voted in this term (`priorVote = none`)
       or has already voted for this candidate (`priorVote = some candId`).
    2. **Log-freshness condition**: the candidate's log `(candLastTerm, candLastIndex)` is at
       least as up-to-date as the voter's log (`isUpToDate voterLog candLastTerm candLastIndex`).

    Models the Rust vote-granting logic in `src/raft.rs:1494–1530`:
    ```rust
    let can_vote = (self.vote == m.from) ||
                   (self.vote == INVALID_ID && self.leader_id == INVALID_ID) || ...;
    if can_vote && self.raft_log.is_up_to_date(m.index, m.log_term) && ...
    ```
    We abstract away: `leader_id` check, priority tie-breaking, pre-vote handling. -/
def voteGranted (voterLog : LogId) (priorVote : Option Nat)
    (candId candLastTerm candLastIndex : Nat) : Bool :=
  (priorVote = none || priorVote = some candId) &&
  isUpToDate voterLog candLastTerm candLastIndex

/-! ## RE1: Empty-voter quorum -/

/-- **RE1** — With an empty voter list, any candidate trivially satisfies the quorum
    condition (`hasQuorum [] _ = true` by definition, vacuous majority). -/
theorem wonInTerm_nil (record : VoteRecord) (term candidate : Nat) :
    wonInTerm [] record term candidate = true := by
  simp [wonInTerm]

/-! ## RE2: Definitional unfolding -/

/-- **RE2** — `wonInTerm` is definitionally equal to `hasQuorum` of the vote-check
    function.  Useful for chaining with `hasQuorum` lemmas from `FVSquad.HasQuorum`. -/
theorem wonInTerm_iff (voters : List Nat) (record : VoteRecord) (term candidate : Nat) :
    wonInTerm voters record term candidate =
    hasQuorum voters (fun voter => decide (record term voter = some candidate)) :=
  rfl

/-! ## RE3: Single-valued vote record -/

/-- **RE3** — The `VoteRecord` assigns at most one candidate per `(term, voter)` pair.

    This is a direct consequence of `VoteRecord` being a function: `record term voter`
    has a unique value.  No explicit axiom about "voting only once" is needed.

    **Significance**: this is the formal model of the Raft §5.2 requirement: "each server
    will vote for at most one candidate in a given term, on a first-come-first-served basis."
    In our model, the VoteRecord function captures the *stable* vote history, not the live
    state change — so single-valuedness is automatic. -/
theorem voteRecord_single_valued (record : VoteRecord) (term voter c1 c2 : Nat)
    (h1 : record term voter = some c1)
    (h2 : record term voter = some c2) :
    c1 = c2 :=
  Option.some.inj (h1 ▸ h2)

/-! ## RE4: Shared voter from two winners -/

/-- **RE4** — If two candidates both win the election in the same term, there is an
    explicit shared voter who voted for both — a direct application of `quorum_intersection_mem`
    (HQ20).

    **Note**: the shared voter must have voted for both `c1` and `c2`.  Since `VoteRecord`
    is single-valued, this forces `c1 = c2` (proved by `electionSafety`, RE5). -/
theorem shared_voter_of_two_winners (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (term c1 c2 : Nat)
    (hw1 : wonInTerm (hd :: tl) record term c1 = true)
    (hw2 : wonInTerm (hd :: tl) record term c2 = true) :
    ∃ w ∈ (hd :: tl),
      record term w = some c1 ∧ record term w = some c2 := by
  simp only [wonInTerm] at hw1 hw2
  obtain ⟨w, hmem, hv1, hv2⟩ :=
    quorum_intersection_mem hd tl
      (fun voter => decide (record term voter = some c1))
      (fun voter => decide (record term voter = some c2))
      hw1 hw2
  simp only [decide_eq_true_eq] at hv1 hv2
  exact ⟨w, hmem, hv1, hv2⟩

/-! ## RE5: ElectionSafety — the main theorem -/

/-- **RE5 — ElectionSafety**: at most one candidate can win an election in any given term.

    If two candidates `c1` and `c2` both win the election in `term` (each receives votes
    from a majority quorum of `voters`), then `c1 = c2`.

    **Proof sketch**:
    1. By `quorum_intersection_mem` (HQ20), any two majority quorums must share a voter `w`.
    2. Voter `w` voted for both `c1` and `c2` in `term`: `record term w = some c1`
       and `record term w = some c2`.
    3. Since `VoteRecord` is a function, `some c1 = some c2`, hence `c1 = c2`.

    **Significance**: This directly formalises the Raft ElectionSafety invariant (§5.2):
    *"At most one leader can be elected in any given term."*  The proof relies on exactly
    two properties: (a) quorum intersection (HQ20, proved in `HasQuorum.lean`), and
    (b) single-valuedness of the vote record (RE3, definitional).

    **Connection to RaftTrace**: this theorem is the key step toward discharging the
    `hqc_preserved` hypothesis in `RaftReachable.step` (see `RaftTrace.lean`).  The full
    discharge requires additionally proving Leader Completeness (future
    `LeaderCompleteness.lean`). -/
theorem electionSafety (hd : Nat) (tl : List Nat) (record : VoteRecord) (term c1 c2 : Nat)
    (hw1 : wonInTerm (hd :: tl) record term c1 = true)
    (hw2 : wonInTerm (hd :: tl) record term c2 = true) :
    c1 = c2 := by
  obtain ⟨w, _, hv1, hv2⟩ := shared_voter_of_two_winners hd tl record term c1 c2 hw1 hw2
  exact Option.some.inj (hv1 ▸ hv2)

/-! ## RE6: Contrapositive of ElectionSafety -/

/-- **RE6** — Contrapositive of `electionSafety`: if `c1 ≠ c2`, they cannot both win
    the election in the same term.

    Useful for proving that a second candidate's election attempt would fail: if `c1`
    has already won, any `c2 ≠ c1` cannot form a winning quorum. -/
theorem electionSafety_ne (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (term c1 c2 : Nat) (hne : c1 ≠ c2) :
    ¬ (wonInTerm (hd :: tl) record term c1 = true ∧
       wonInTerm (hd :: tl) record term c2 = true) :=
  fun ⟨hw1, hw2⟩ => hne (electionSafety hd tl record term c1 c2 hw1 hw2)

/-! ## RE7–RE10: Vote-granting properties -/

/-- **RE7** — If a vote is granted, the candidate's log is at least as up-to-date
    as the voter's log.

    This captures the Raft §5.4.1 log-freshness requirement: a voter only grants a vote
    if the candidate's `(lastLogTerm, lastLogIndex)` is at least as up-to-date as its own.
    Without this condition, a candidate with a stale log could win and lose committed entries.

    Corresponds to `self.raft_log.is_up_to_date(m.index, m.log_term)` in `src/raft.rs:1500`. -/
theorem voteGranted_isUpToDate (voterLog : LogId) (priorVote : Option Nat)
    (candId candLastTerm candLastIndex : Nat)
    (hg : voteGranted voterLog priorVote candId candLastTerm candLastIndex = true) :
    isUpToDate voterLog candLastTerm candLastIndex = true := by
  simp only [voteGranted, Bool.and_eq_true] at hg
  exact hg.2

/-- **RE8** — If a vote is granted, the voter's prior vote was either absent or for
    the same candidate.

    This captures the single-vote-per-term rule: a voter only grants a vote if it
    either hasn't voted yet (`priorVote = none`) or is repeating a vote for the same
    candidate (`priorVote = some candId`). -/
theorem voteGranted_priorVote_none_or_self (voterLog : LogId) (priorVote : Option Nat)
    (candId candLastTerm candLastIndex : Nat)
    (hg : voteGranted voterLog priorVote candId candLastTerm candLastIndex = true) :
    priorVote = none ∨ priorVote = some candId := by
  simp only [voteGranted, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hg
  exact hg.1

/-- **RE9** — If a voter has already voted for candidate `c1` and `c1 ≠ c2`, it will
    not grant a vote to candidate `c2`.

    This is the formal model of the §5.2 "first-come-first-served" rule: once a vote
    is cast for `c1`, no vote can be cast for any other candidate in the same term. -/
theorem not_voteGranted_of_other_prior (voterLog : LogId)
    (c1 c2 candLastTerm candLastIndex : Nat) (hne : c1 ≠ c2) :
    voteGranted voterLog (some c1) c2 candLastTerm candLastIndex = false := by
  simp only [voteGranted, Bool.and_eq_false_iff, Bool.or_eq_false_iff]
  left
  constructor
  · simp
  · rw [decide_eq_false_iff_not]
    intro h
    exact hne (Option.some.inj h)

/-- **RE10** — If a vote is granted and the prior vote was already set, it must have
    been for the same candidate.

    This is the "repeat vote" case: a voter can only grant a vote to the candidate it
    already voted for. -/
theorem voteGranted_and_prior_eq (voterLog : LogId) (c1 candId candLastTerm candLastIndex : Nat)
    (hg : voteGranted voterLog (some c1) candId candLastTerm candLastIndex = true) :
    c1 = candId := by
  simp only [voteGranted, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hg
  cases hg.1 with
  | inl h => simp at h
  | inr h => exact Option.some.inj h

/-! ## RE11: Winner implies a voter -/

/-- **RE11** — If a candidate wins an election with nonempty voters, there exists at
    least one voter who cast a vote for that candidate.

    **Proof**: `wonInTerm (hd :: tl)` means `hasQuorum (hd :: tl) f = true` for
    `f = fun v => decide (record term v = some candidate)`.  A non-trivially-true quorum
    (nonempty voter list) implies at least one voter where `f voter = true`, which means
    at least one voter voted for the candidate. -/
theorem wonInTerm_implies_some_voter (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (term candidate : Nat)
    (hw : wonInTerm (hd :: tl) record term candidate = true) :
    ∃ w ∈ (hd :: tl), record term w = some candidate := by
  simp only [wonInTerm] at hw
  obtain ⟨w, hmem, hv, _⟩ :=
    quorum_intersection_mem hd tl
      (fun voter => decide (record term voter = some candidate))
      (fun voter => decide (record term voter = some candidate))
      hw hw
  exact ⟨w, hmem, by simp only [decide_eq_true_eq] at hv; exact hv⟩

/-! ## RE12: Singleton cluster -/

/-- **RE12** — In a single-voter cluster `[voter]`, candidate `candidate` wins iff
    that voter voted for `candidate`.

    **Proof**: `wonInTerm [voter] record term candidate = hasQuorum [voter] f`.
    By `hasQuorum_singleton_self` (HQ15), `hasQuorum [voter] f = true` iff `f voter = true`,
    i.e., `decide (record term voter = some candidate) = true`,
    i.e., `record term voter = some candidate`. -/
theorem wonInTerm_singleton_iff (voter : Nat) (record : VoteRecord) (term candidate : Nat) :
    wonInTerm [voter] record term candidate = true ↔
    record term voter = some candidate := by
  constructor
  · intro h
    obtain ⟨w, hmem, hvote⟩ := wonInTerm_implies_some_voter voter [] record term candidate h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rw [← hmem]; exact hvote
  · intro h
    simp only [wonInTerm]
    apply hasQuorum_singleton_self
    simp [h]

/-! ## RE13: Candidate voting for itself wins in singleton cluster -/

/-- **RE13** — In a singleton cluster where `voter = candidate` and the candidate
    voted for itself (`record term candidate = some candidate`), the candidate wins.

    This models the Raft `become_candidate` behaviour: the first action on becoming a
    candidate is to vote for oneself (`src/raft.rs:1190`: `self.vote = id`). -/
theorem wonInTerm_singleton_self (record : VoteRecord) (term candidate : Nat)
    (hvoted : record term candidate = some candidate) :
    wonInTerm [candidate] record term candidate = true := by
  rw [wonInTerm_singleton_iff]
  exact hvoted

/-! ## RE14: Two leaders in same term → same node -/

/-- **RE14** — If two nodes `n1` and `n2` both won elections in `term` with nonempty
    voters, they are the same node ID.

    This is the NodeID form of `electionSafety` (RE5): the two "leader IDs" that won
    their respective elections must be equal. -/
theorem electionSafety_two_leaders (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (term n1 n2 : Nat)
    (hw1 : wonInTerm (hd :: tl) record term n1 = true)
    (hw2 : wonInTerm (hd :: tl) record term n2 = true) :
    n1 = n2 :=
  electionSafety hd tl record term n1 n2 hw1 hw2

/-! ## RE15: Voter voted for the actual winner -/

/-- **RE15** — If voter `w` voted for `candidate` and `c2` also won the election, then
    voter `w` also voted for `c2` (because `c2 = candidate` by RE5).

    This is the "consistent ballot" property: in any given term, a voter's ballot is
    uniquely associated with the winner.  No voter's ballot can support two different
    outcomes. -/
theorem wonInTerm_voter_voted (hd : Nat) (tl : List Nat) (record : VoteRecord)
    (term candidate c2 w : Nat)
    (hw : wonInTerm (hd :: tl) record term candidate = true)
    (hw2 : wonInTerm (hd :: tl) record term c2 = true)
    (hvote : record term w = some candidate) :
    record term w = some c2 := by
  have heq : c2 = candidate := electionSafety hd tl record term c2 candidate hw2 hw
  rw [heq]; exact hvote

/-! ## State transition functions

These model the `become_follower`, `become_candidate`, and `become_leader` functions in
`src/raft.rs:1155–1283`.  The Rust functions are imperative and mutate many fields; the
Lean model captures only the election-relevant state (`currentTerm`, `votedFor`, `role`).

## Theorem Table (Transitions)

| ID   | Name                                   | Status    | Description |
|------|----------------------------------------|-----------|-------------|
| RT1  | `becomeFollower_term`                  | ✅ proved  | Term after becomeFollower equals the given term |
| RT2  | `becomeFollower_role`                  | ✅ proved  | Role is Follower after becomeFollower |
| RT3  | `becomeFollower_vote_reset`            | ✅ proved  | Vote is reset to none when term strictly increases |
| RT4  | `becomeFollower_vote_preserved`        | ✅ proved  | Vote is preserved when term stays the same |
| RT5  | `becomeFollower_term_monotone`         | ✅ proved  | becomeFollower never decreases the term |
| RT6  | `becomeCandidate_term`                 | ✅ proved  | Term after becomeCandidate = old term + 1 |
| RT7  | `becomeCandidate_role`                 | ✅ proved  | Role is Candidate after becomeCandidate |
| RT8  | `becomeCandidate_vote`                 | ✅ proved  | Candidate votes for itself |
| RT9  | `becomeCandidate_term_strict`          | ✅ proved  | becomeCandidate strictly increases the term |
| RT10 | `becomeLeader_role`                    | ✅ proved  | Role is Leader after becomeLeader |
| RT11 | `becomeLeader_term_unchanged`          | ✅ proved  | Term is unchanged by becomeLeader |
| RT12 | `becomeLeader_vote_unchanged`          | ✅ proved  | Vote is unchanged by becomeLeader |
| RT13 | `becomeLeader_voted_for_self`          | ✅ proved  | After becomeCandidate then becomeLeader, leader voted for itself |
| RT14 | `becomeFollower_from_candidate_resets` | ✅ proved  | Follower after candidate with same term retains vote |
| RT15 | `term_monotone_sequence`               | ✅ proved  | Term only increases: becomeFollower ≥ old; becomeCandidate > old |
-/

/-! ### `becomeFollower`

Models `Raft::become_follower(term, leader_id)` from `src/raft.rs:1155`.

The `reset` helper (line 1015) sets `self.vote = INVALID_ID` only when `term != self.term`.
We model this: vote is cleared iff `newTerm ≠ s.currentTerm`. -/
def becomeFollower (s : NodeState) (newTerm : Nat) : NodeState :=
  { currentTerm := newTerm
    votedFor    := if newTerm != s.currentTerm then none else s.votedFor
    role        := NodeRole.Follower }

/-! ### `becomeCandidate`

Models `Raft::become_candidate()` from `src/raft.rs:1183`.

Precondition (Rust): `self.state ≠ Leader` (panics otherwise).
Effect: term ← term+1, vote ← self.id, role ← Candidate. -/
def becomeCandidate (s : NodeState) (selfId : Nat) : NodeState :=
  { currentTerm := s.currentTerm + 1
    votedFor    := some selfId
    role        := NodeRole.Candidate }

/-! ### `becomeLeader`

Models `Raft::become_leader()` from `src/raft.rs:1233`.

Precondition (Rust): `self.state ≠ Follower`.
Effect: role ← Leader, term and vote unchanged. -/
def becomeLeader (s : NodeState) : NodeState :=
  { s with role := NodeRole.Leader }

-- ─────────────────────────────────────────────────────────────
-- RT1–RT5: becomeFollower properties
-- ─────────────────────────────────────────────────────────────

/-- **RT1** `becomeFollower` sets the term to `newTerm`. -/
theorem RT1_becomeFollower_term (s : NodeState) (newTerm : Nat) :
    (becomeFollower s newTerm).currentTerm = newTerm := by
  simp [becomeFollower]

/-- **RT2** `becomeFollower` sets the role to `Follower`. -/
theorem RT2_becomeFollower_role (s : NodeState) (newTerm : Nat) :
    (becomeFollower s newTerm).role = NodeRole.Follower := by
  simp [becomeFollower]

/-- **RT3** When the term strictly increases, `becomeFollower` clears the vote. -/
theorem RT3_becomeFollower_vote_reset (s : NodeState) (newTerm : Nat)
    (h : newTerm ≠ s.currentTerm) :
    (becomeFollower s newTerm).votedFor = none := by
  simp [becomeFollower, h]

/-- **RT4** When the term stays the same, `becomeFollower` preserves the vote. -/
theorem RT4_becomeFollower_vote_preserved (s : NodeState) (newTerm : Nat)
    (h : newTerm = s.currentTerm) :
    (becomeFollower s newTerm).votedFor = s.votedFor := by
  simp [becomeFollower, h]

/-- **RT5** `becomeFollower` never decreases the term (caller must pass `newTerm ≥ s.currentTerm`).
    This theorem states the monotonicity direction: the new state's term equals `newTerm`. -/
theorem RT5_becomeFollower_term_monotone (s : NodeState) (newTerm : Nat)
    (h : newTerm ≥ s.currentTerm) :
    (becomeFollower s newTerm).currentTerm ≥ s.currentTerm := by
  simp [becomeFollower, h]

-- ─────────────────────────────────────────────────────────────
-- RT6–RT9: becomeCandidate properties
-- ─────────────────────────────────────────────────────────────

/-- **RT6** `becomeCandidate` sets the term to `s.currentTerm + 1`. -/
theorem RT6_becomeCandidate_term (s : NodeState) (selfId : Nat) :
    (becomeCandidate s selfId).currentTerm = s.currentTerm + 1 := by
  simp [becomeCandidate]

/-- **RT7** `becomeCandidate` sets the role to `Candidate`. -/
theorem RT7_becomeCandidate_role (s : NodeState) (selfId : Nat) :
    (becomeCandidate s selfId).role = NodeRole.Candidate := by
  simp [becomeCandidate]

/-- **RT8** `becomeCandidate` records a vote for `selfId` (the node votes for itself). -/
theorem RT8_becomeCandidate_vote (s : NodeState) (selfId : Nat) :
    (becomeCandidate s selfId).votedFor = some selfId := by
  simp [becomeCandidate]

/-- **RT9** `becomeCandidate` strictly increases the term. -/
theorem RT9_becomeCandidate_term_strict (s : NodeState) (selfId : Nat) :
    (becomeCandidate s selfId).currentTerm > s.currentTerm := by
  simp [becomeCandidate]

-- ─────────────────────────────────────────────────────────────
-- RT10–RT12: becomeLeader properties
-- ─────────────────────────────────────────────────────────────

/-- **RT10** `becomeLeader` sets the role to `Leader`. -/
theorem RT10_becomeLeader_role (s : NodeState) :
    (becomeLeader s).role = NodeRole.Leader := by
  simp [becomeLeader]

/-- **RT11** `becomeLeader` leaves the term unchanged. -/
theorem RT11_becomeLeader_term_unchanged (s : NodeState) :
    (becomeLeader s).currentTerm = s.currentTerm := by
  simp [becomeLeader]

/-- **RT12** `becomeLeader` leaves the vote unchanged. -/
theorem RT12_becomeLeader_vote_unchanged (s : NodeState) :
    (becomeLeader s).votedFor = s.votedFor := by
  simp [becomeLeader]

-- ─────────────────────────────────────────────────────────────
-- RT13–RT15: compound properties
-- ─────────────────────────────────────────────────────────────

/-- **RT13** After `becomeCandidate` followed by `becomeLeader`, the leader voted for itself.
    This is invariant I4 from the informal spec: every leader voted for itself while
    campaigning.  The leader's `votedFor` field remains `some selfId` because `becomeLeader`
    does not touch the vote. -/
theorem RT13_becomeLeader_voted_for_self (s : NodeState) (selfId : Nat) :
    (becomeLeader (becomeCandidate s selfId)).votedFor = some selfId := by
  simp [becomeLeader, becomeCandidate]

/-- **RT14** If a node is a candidate in term `t` and calls `becomeFollower` with the same
    term `t`, the vote is preserved (no vote reset for same-term transitions).
    This models the Rust `reset` path where `self.term == term` → vote unchanged. -/
theorem RT14_becomeFollower_same_term_preserves_vote (s : NodeState) (selfId : Nat) :
    (becomeFollower (becomeCandidate s selfId) (s.currentTerm + 1)).votedFor = some selfId := by
  simp [becomeFollower, becomeCandidate]

/-- **RT15** Term monotonicity across both transitions:
    - `becomeFollower newTerm` produces term = `newTerm` (caller guarantees `newTerm ≥ old`)
    - `becomeCandidate` produces term = `old + 1 > old`
    This combines RT5 and RT9 into a single statement for use in inductive arguments. -/
theorem RT15_term_monotone_sequence (s : NodeState) (selfId : Nat) (newTerm : Nat)
    (h : newTerm ≥ s.currentTerm) :
    (becomeFollower s newTerm).currentTerm ≥ s.currentTerm ∧
    (becomeCandidate s selfId).currentTerm > s.currentTerm := by
  exact ⟨RT5_becomeFollower_term_monotone s newTerm h,
         RT9_becomeCandidate_term_strict s selfId⟩

/-! ## RI1–RI15: processVoteRequest and multi-step invariants

These theorems formalise:
- **`processVoteRequest`**: the full vote-granting state transition — first bump the term if
  the candidate's term is higher (`becomeFollower`), then grant the vote if conditions hold.
  This models the Rust `Raft::step` path for `MessageType::MsgRequestVote`.
- **RI1–RI5**: correctness of `processVoteRequest`.
- **RI6–RI10**: term arithmetic under sequences of state transitions.
- **RI11–RI15**: cross-node / multi-step invariants connecting the individual transition
  theorems to cluster-level properties.

### processVoteRequest theorem table

| ID   | Name                                          | Status    | Description |
|------|-----------------------------------------------|-----------|-------------|
| RI1  | `processVoteRequest_grants_vote`              | ✅ proved  | Vote granted when conditions met |
| RI2  | `processVoteRequest_denies_other_vote`        | ✅ proved  | Vote denied when already voted for different candidate |
| RI3  | `processVoteRequest_idempotent`               | ✅ proved  | Re-voting for same candidate is idempotent |
| RI4  | `processVoteRequest_term_nondecreasing`       | ✅ proved  | Term never decreases after processing vote request |
| RI5  | `processVoteRequest_higher_term_clears_vote`  | ✅ proved  | Higher-term request clears prior vote before checking |
| RI6  | `double_becomeCandidate_term`                 | ✅ proved  | Two consecutive becomeCandidate calls increment term by 2 |
| RI7  | `becomeCandidate_after_becomeFollower_term`   | ✅ proved  | becomeCandidate after becomeFollower(t) gives term t+1 |
| RI8  | `becomeFollower_idempotent_on_term`           | ✅ proved  | becomeFollower twice with same term: term unchanged |
| RI9  | `becomeFollower_chain_term`                   | ✅ proved  | becomeFollower(t1) then becomeFollower(t2): term = t2 |
| RI10 | `becomeLeader_after_sequence_term`            | ✅ proved  | becomeLeader ∘ becomeCandidate ∘ becomeFollower term arithmetic |
| RI11 | `leader_voted_self_via_candidate`             | ✅ proved  | I4: any leader reached via becomeCandidate voted for itself |
| RI12 | `candidate_term_gt_follower_term`             | ✅ proved  | Candidate always has a strictly higher term than the follower it preceded |
| RI13 | `wonInTerm_consistent_with_vote_record`       | ✅ proved  | VoteRecord consistent with actual votes → winner uniqueness |
| RI14 | `processVoteRequest_voted_for_is_cand`        | ✅ proved  | After granting vote, votedFor = some candId |
| RI15 | `two_leaders_same_term_same_id`               | ✅ proved  | Two nodes that won elections in the same term are the same node |
-/

/-! ### `processVoteRequest`

Models the full vote-response state transition when a node receives a `RequestVote` RPC:
1. If `candTerm > s.currentTerm`, call `becomeFollower candTerm` (term bump + vote clear).
2. If the vote-granting conditions hold, set `votedFor := some candId`.

**Abstracted away**: message sending, message filtering, pre-vote phase.
**Parameters**: `voterLog : LogId` — the voter's own log state (not in `NodeState`; kept
separate since `NodeState` models only the election-relevant persistent fields). -/
def processVoteRequest (s : NodeState) (voterLog : LogId)
    (candId candTerm candLastTerm candLastIndex : Nat) : NodeState :=
  if candTerm > s.currentTerm then
    if voteGranted voterLog none candId candLastTerm candLastIndex then
      { currentTerm := candTerm, votedFor := some candId, role := NodeRole.Follower }
    else
      becomeFollower s candTerm
  else
    if voteGranted voterLog s.votedFor candId candLastTerm candLastIndex then
      { s with votedFor := some candId }
    else
      s

-- ─────────────────────────────────────────────────────────────
-- RI1–RI5: processVoteRequest correctness
-- ─────────────────────────────────────────────────────────────

/-- **RI1** When `voteGranted` returns `true`, `processVoteRequest` sets `votedFor` to
    `some candId`.  This is the positive case: the vote is granted. -/
theorem RI1_processVoteRequest_grants_vote
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat)
    (hg : voteGranted voterLog
            (if candTerm > s.currentTerm then none else s.votedFor)
            candId candLastTerm candLastIndex = true) :
    (processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex).votedFor =
      some candId := by
  by_cases h : candTerm > s.currentTerm
  · rw [show (if candTerm > s.currentTerm then (none : Option Nat) else s.votedFor) = none
        from if_pos h] at hg
    simp [processVoteRequest, h, hg]
  · rw [show (if candTerm > s.currentTerm then (none : Option Nat) else s.votedFor) = s.votedFor
        from if_neg h] at hg
    simp [processVoteRequest, h, hg]

/-- **RI2** When a node already voted for a *different* candidate `c1 ≠ candId` and the
    candidate's term does not exceed the current term, the vote is **denied** and `votedFor`
    stays `some c1`. -/
theorem RI2_processVoteRequest_denies_other_vote
    (s : NodeState) (voterLog : LogId) (c1 candId candTerm candLastTerm candLastIndex : Nat)
    (hterm : ¬ (candTerm > s.currentTerm))
    (hne   : c1 ≠ candId)
    (hvote : s.votedFor = some c1) :
    (processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex).votedFor =
      some c1 := by
  have hd : voteGranted voterLog (some c1) candId candLastTerm candLastIndex = false :=
    not_voteGranted_of_other_prior voterLog c1 candId candLastTerm candLastIndex hne
  simp [processVoteRequest, hterm, hvote, hd]

/-- **RI3** Processing a vote request for the *same* candidate twice is idempotent: the
    second call leaves the state unchanged.  This captures the Raft guarantee that a node
    "remembers" its vote across retransmissions. -/
theorem RI3_processVoteRequest_idempotent
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat)
    (hterm : ¬ (candTerm > s.currentTerm))
    (hvote : s.votedFor = some candId) :
    processVoteRequest
      (processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex)
      voterLog candId candTerm candLastTerm candLastIndex =
    processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex := by
  cases hg : voteGranted voterLog (some candId) candId candLastTerm candLastIndex
  · -- vote denied: inner processVoteRequest returns s unchanged, outer is same
    simp [processVoteRequest, hterm, hvote, hg]
  · -- vote granted: inner returns {s with votedFor := some candId} = s (already set)
    -- outer applied to that: same candTerm, same term, same votedFor
    simp [processVoteRequest, hterm, hvote, hg]

/-- **RI4** `processVoteRequest` never decreases the current term. -/
theorem RI4_processVoteRequest_term_nondecreasing
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat) :
    (processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex).currentTerm ≥
      s.currentTerm := by
  by_cases h : candTerm > s.currentTerm
  · cases hg : voteGranted voterLog none candId candLastTerm candLastIndex
    · simp [processVoteRequest, h, hg, becomeFollower]; omega
    · simp [processVoteRequest, h, hg]; omega
  · cases hg : voteGranted voterLog s.votedFor candId candLastTerm candLastIndex
    · simp [processVoteRequest, h, hg]
    · simp [processVoteRequest, h, hg]

/-- **RI5** When a candidate arrives with a strictly higher term, `processVoteRequest` first
    bumps the node's term to `candTerm` (via `becomeFollower`) before checking vote-granting
    conditions.  The resulting `currentTerm` equals `candTerm`. -/
theorem RI5_processVoteRequest_higher_term_clears_vote
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat)
    (hterm : candTerm > s.currentTerm) :
    (processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex).currentTerm =
      candTerm := by
  cases hg : voteGranted voterLog none candId candLastTerm candLastIndex
  · simp [processVoteRequest, hterm, hg, becomeFollower]
  · simp [processVoteRequest, hterm, hg]

-- ─────────────────────────────────────────────────────────────
-- RI6–RI10: term arithmetic under sequences of transitions
-- ─────────────────────────────────────────────────────────────

/-- **RI6** Applying `becomeCandidate` twice increments the term by exactly 2.
    Each call adds 1; they compose to add 2.  This models the pattern where a candidate
    times out and calls another election. -/
theorem RI6_double_becomeCandidate_term (s : NodeState) (selfId : Nat) :
    (becomeCandidate (becomeCandidate s selfId) selfId).currentTerm = s.currentTerm + 2 := by
  simp [becomeCandidate]

/-- **RI7** `becomeCandidate` after `becomeFollower(t)` gives term `t + 1`.  This is the
    normal election flow: a node receives a higher term, steps down to follower, then starts
    a new election. -/
theorem RI7_becomeCandidate_after_becomeFollower_term (s : NodeState) (t selfId : Nat) :
    (becomeCandidate (becomeFollower s t) selfId).currentTerm = t + 1 := by
  simp [becomeCandidate, becomeFollower]

/-- **RI8** Calling `becomeFollower` twice with the same term is idempotent on the term. -/
theorem RI8_becomeFollower_idempotent_on_term (s : NodeState) (t : Nat) :
    (becomeFollower (becomeFollower s t) t).currentTerm = t := by
  simp [becomeFollower]

/-- **RI9** Applying `becomeFollower t1` then `becomeFollower t2` (regardless of order of
    `t1`, `t2`) produces term `t2`.  The final `becomeFollower` always wins on the term. -/
theorem RI9_becomeFollower_chain_term (s : NodeState) (t1 t2 : Nat) :
    (becomeFollower (becomeFollower s t1) t2).currentTerm = t2 := by
  simp [becomeFollower]

/-- **RI10** Full election sequence: `becomeFollower(t)` → `becomeCandidate` → `becomeLeader`
    produces a leader with term `t + 1`.  This captures the Raft election lifecycle in
    terms of the term field. -/
theorem RI10_becomeLeader_after_sequence_term (s : NodeState) (t selfId : Nat) :
    (becomeLeader (becomeCandidate (becomeFollower s t) selfId)).currentTerm = t + 1 := by
  simp [becomeLeader, becomeCandidate, becomeFollower]

-- ─────────────────────────────────────────────────────────────
-- RI11–RI15: cross-node invariants
-- ─────────────────────────────────────────────────────────────

/-- **RI11** Any leader reached through the canonical election sequence
    (`becomeFollower` → `becomeCandidate` → `becomeLeader`) has `votedFor = some selfId`.
    This is **Invariant I4** from the informal spec: every leader voted for itself.
    The proof chains RT8 (becomeCandidate sets vote to selfId) and RT12 (becomeLeader
    preserves vote). -/
theorem RI11_leader_voted_self_via_candidate (s : NodeState) (t selfId : Nat) :
    (becomeLeader (becomeCandidate (becomeFollower s t) selfId)).votedFor = some selfId := by
  simp [becomeLeader, becomeCandidate, becomeFollower]

/-- **RI12** A candidate's term is always strictly greater than the follower term it started
    from.  Concretely: starting from any state, `becomeFollower(t)` then `becomeCandidate`
    gives a state with `currentTerm > t`.  This is used in liveness arguments: a candidate
    always campaigns in a fresh term. -/
theorem RI12_candidate_term_gt_follower_term (s : NodeState) (t selfId : Nat) :
    (becomeCandidate (becomeFollower s t) selfId).currentTerm > t := by
  simp [becomeCandidate, becomeFollower]

/-- **RI13** **VoteRecord consistency → winner uniqueness**.
    If two candidates both win in the same term using the *same* vote record, they are
    the same candidate.  This is `electionSafety` (RE5) restated as a consistency property:
    a single consistent vote record cannot certify two different winners in the same term.
    The proof is immediate from RE5. -/
theorem RI13_wonInTerm_consistent_with_vote_record
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (term c1 c2 : Nat)
    (hw1 : wonInTerm (hd :: tl) record term c1 = true)
    (hw2 : wonInTerm (hd :: tl) record term c2 = true) :
    c1 = c2 :=
  electionSafety hd tl record term c1 c2 hw1 hw2

/-- **RI14** `processVoteRequest` sets `votedFor = some candId` whenever the vote is granted.
    This is a direct combination of RI1 and the logic of `voteGranted`:
    if conditions are met, `votedFor` is updated. -/
theorem RI14_processVoteRequest_voted_for_is_cand
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat)
    (hg : voteGranted voterLog
            (if candTerm > s.currentTerm then none else s.votedFor)
            candId candLastTerm candLastIndex = true) :
    (processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex).votedFor =
      some candId :=
  RI1_processVoteRequest_grants_vote s voterLog candId candTerm candLastTerm candLastIndex hg

/-- **RI15** **Two election winners in the same term are the same candidate**.
    If both `c1` and `c2` received quorum votes in `term` from the same voter list using
    the same vote record, then `c1 = c2`.  This is the definitive cluster-level election
    safety property: no split leadership within a term.

    The proof is a direct application of `electionSafety` (RE5), which in turn relies on:
    1. `HQ20` (quorum intersection): any two majority quorums share a voter.
    2. `voteRecord_single_valued` (RE3): each voter votes for at most one candidate per term.
-/
theorem RI15_two_leaders_same_term_same_id
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (term c1 c2 : Nat)
    (hw1 : wonInTerm (hd :: tl) record term c1 = true)
    (hw2 : wonInTerm (hd :: tl) record term c2 = true) :
    c1 = c2 :=
  electionSafety hd tl record term c1 c2 hw1 hw2

-- ─────────────────────────────────────────────────────────────
-- RV1–RV8: voteGranted characterisation and processVoteRequest structure
-- ─────────────────────────────────────────────────────────────

/-!
## Section RV — voteGranted / processVoteRequest structural theorems

These theorems characterise the precise input–output relationship of `voteGranted`
(complementing the one-way implications RE7/RE8/RE9) and the structural properties of
`processVoteRequest` beyond the RI series.

| ID   | Name                                           | Status    | Description |
|------|------------------------------------------------|-----------|-------------|
| RV1  | `RV1_voteGranted_true_iff`                     | ✅ proved  | Biconditional: voteGranted = true ↔ prior-ok ∧ isUpToDate |
| RV2  | `RV2_voteGranted_false_of_not_upToDate`        | ✅ proved  | ¬isUpToDate → voteGranted = false |
| RV3  | `RV3_voteGranted_true_of_none_and_upToDate`    | ✅ proved  | prior=none ∧ isUpToDate → voteGranted = true |
| RV4  | `RV4_processVoteRequest_currentTerm`           | ✅ proved  | Resulting term = max(s.currentTerm, candTerm) |
| RV5  | `RV5_processVoteRequest_role_unchanged_low_term` | ✅ proved | ¬(candTerm > s.currentTerm) → role unchanged |
| RV6  | `RV6_processVoteRequest_higher_term_granted_state` | ✅ proved | Higher term + granted → full resulting state |
| RV7  | `RV7_processVoteRequest_higher_term_denied_state`  | ✅ proved | Higher term + denied → becomeFollower state  |
| RV8  | `RV8_wonInTerm_of_all_voters_voted`            | ✅ proved  | All voters voted → wonInTerm = true |
-/

/-- **RV1** Biconditional: `voteGranted voterLog priorVote candId candLastTerm candLastIndex = true`
    iff (a) the prior vote is `none` or `some candId`, AND (b) the candidate's log is at
    least as up-to-date as the voter's log.

    This is the explicit iff form of the definition, complementing the one-way implications
    RE7 (`voteGranted_isUpToDate`) and RE8 (`voteGranted_priorVote_none_or_self`). -/
theorem RV1_voteGranted_true_iff (voterLog : LogId) (priorVote : Option Nat)
    (candId candLastTerm candLastIndex : Nat) :
    voteGranted voterLog priorVote candId candLastTerm candLastIndex = true ↔
    (priorVote = none ∨ priorVote = some candId) ∧
    isUpToDate voterLog candLastTerm candLastIndex = true := by
  constructor
  · intro h
    exact ⟨voteGranted_priorVote_none_or_self voterLog priorVote candId candLastTerm candLastIndex h,
           voteGranted_isUpToDate voterLog priorVote candId candLastTerm candLastIndex h⟩
  · intro ⟨h1, h2⟩
    simp only [voteGranted, Bool.and_eq_true]
    refine ⟨?_, h2⟩
    rcases h1 with rfl | rfl <;> simp

/-- **RV2** If the candidate's log is *not* at least as up-to-date as the voter's log,
    then `voteGranted` is `false` — regardless of the prior-vote status.  This is the
    contrapositive of RE7. -/
theorem RV2_voteGranted_false_of_not_upToDate (voterLog : LogId) (priorVote : Option Nat)
    (candId candLastTerm candLastIndex : Nat)
    (hiu : isUpToDate voterLog candLastTerm candLastIndex = false) :
    voteGranted voterLog priorVote candId candLastTerm candLastIndex = false := by
  simp [voteGranted, hiu]

/-- **RV3** If the voter has not yet voted (`priorVote = none`) and the candidate's log is
    at least as up-to-date as the voter's log, then `voteGranted` is `true`.

    This is the "easy grant" case: a fresh voter with an up-to-date candidate. -/
theorem RV3_voteGranted_true_of_none_and_upToDate (voterLog : LogId)
    (candId candLastTerm candLastIndex : Nat)
    (hiu : isUpToDate voterLog candLastTerm candLastIndex = true) :
    voteGranted voterLog none candId candLastTerm candLastIndex = true := by
  simp [voteGranted, hiu]

/-- **RV4** The `currentTerm` of the node after `processVoteRequest` is the maximum of
    `s.currentTerm` and `candTerm`.

    - If `candTerm > s.currentTerm`: the node adopts the higher term (Raft term-update rule).
    - If `candTerm ≤ s.currentTerm`: the node's term is unchanged. -/
theorem RV4_processVoteRequest_currentTerm
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat) :
    (processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex).currentTerm =
    max s.currentTerm candTerm := by
  by_cases h : candTerm > s.currentTerm
  · simp only [processVoteRequest, if_pos h]
    cases voteGranted voterLog none candId candLastTerm candLastIndex <;>
    simp [becomeFollower] <;> omega
  · simp only [processVoteRequest, if_neg h]
    cases voteGranted voterLog s.votedFor candId candLastTerm candLastIndex <;> simp <;> omega

/-- **RV5** When `candTerm ≤ s.currentTerm` (same term or lower), `processVoteRequest`
    never changes the node's `role`.  The role can only change via `becomeFollower`, which
    only fires when `candTerm > s.currentTerm`. -/
theorem RV5_processVoteRequest_role_unchanged_low_term
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat)
    (hle : ¬ (candTerm > s.currentTerm)) :
    (processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex).role = s.role := by
  simp only [processVoteRequest, if_neg hle]
  cases voteGranted voterLog s.votedFor candId candLastTerm candLastIndex <;> rfl

/-- **RV6** When `candTerm > s.currentTerm` **and** `voteGranted` returns `true` (with
    `priorVote = none`, since the node steps to a fresh term), the full resulting state is:
    `currentTerm = candTerm`, `votedFor = some candId`, `role = Follower`. -/
theorem RV6_processVoteRequest_higher_term_granted_state
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat)
    (hgt  : candTerm > s.currentTerm)
    (hg   : voteGranted voterLog none candId candLastTerm candLastIndex = true) :
    processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex =
    { currentTerm := candTerm, votedFor := some candId, role := NodeRole.Follower } := by
  simp [processVoteRequest, hgt, hg]

/-- **RV7** When `candTerm > s.currentTerm` **and** `voteGranted` returns `false` (candidate
    log not up-to-date), the result is `becomeFollower s candTerm`: the node adopts the
    higher term but does **not** record a vote. -/
theorem RV7_processVoteRequest_higher_term_denied_state
    (s : NodeState) (voterLog : LogId) (candId candTerm candLastTerm candLastIndex : Nat)
    (hgt  : candTerm > s.currentTerm)
    (hd   : voteGranted voterLog none candId candLastTerm candLastIndex = false) :
    processVoteRequest s voterLog candId candTerm candLastTerm candLastIndex =
    becomeFollower s candTerm := by
  simp [processVoteRequest, hgt, hd]

/-- **RV8** If every voter in `voters` has voted for `candId` in `term` according to `record`,
    then `wonInTerm voters record term candId = true`.

    This connects individual vote records to the cluster-level election outcome: when the entire
    voter list is a superset of the winning quorum (because *all* voted), the candidate wins. -/
theorem RV8_wonInTerm_of_all_voters_voted
    (voters : List Nat) (record : VoteRecord) (term candId : Nat)
    (hall : ∀ v ∈ voters, record term v = some candId) :
    wonInTerm voters record term candId = true := by
  simp only [wonInTerm]
  apply hasQuorum_true_of_all_in
  intro v hv
  simp [decide_eq_true_eq, hall v hv]

/-! ## Evaluation examples -/

-- In a 3-voter cluster [1, 2, 3], if voters 1 and 2 voted for candidate 5, then 5 wins.
#eval wonInTerm [1, 2, 3] (fun t v => if t == 1 && (v == 1 || v == 2) then some 5 else none) 1 5
-- true: voters {1,2} form a majority (2 ≥ 2)

-- Candidate 7 does not win with only 1 vote in a 3-voter cluster.
#eval wonInTerm [1, 2, 3] (fun t v => if t == 1 && v == 3 then some 7 else none) 1 7
-- false: only 1 of 3 voters → not a majority

-- In a single-voter cluster, the sole voter's choice wins.
#eval wonInTerm [42] (fun _ v => if v == 42 then some (42 : Nat) else none) 1 42
-- true: single voter voted for 42

-- Transition function examples
#eval becomeCandidate { currentTerm := 1, votedFor := none, role := NodeRole.Follower } 42
-- { currentTerm := 2, votedFor := some 42, role := Candidate }

#eval becomeLeader (becomeCandidate { currentTerm := 1, votedFor := none, role := NodeRole.Follower } 42)
-- { currentTerm := 2, votedFor := some 42, role := Leader }

#eval becomeFollower { currentTerm := 1, votedFor := some 42, role := NodeRole.Candidate } 3
-- { currentTerm := 3, votedFor := none, role := Follower }  (vote cleared — new term)

#eval becomeFollower { currentTerm := 2, votedFor := some 42, role := NodeRole.Candidate } 2
-- { currentTerm := 2, votedFor := some 42, role := Follower }  (vote preserved — same term)

end FVSquad.RaftElection
