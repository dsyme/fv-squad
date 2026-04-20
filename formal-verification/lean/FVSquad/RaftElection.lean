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

end FVSquad.RaftElection
