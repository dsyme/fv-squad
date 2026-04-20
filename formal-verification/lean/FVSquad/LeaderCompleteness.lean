import FVSquad.RaftElection
import FVSquad.RaftSafety

/-!
# LeaderCompleteness — Composing Election Safety with Log Safety

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file formalises the **Leader Completeness** property of the Raft consensus protocol
(§5.4.1 of the Raft paper) and connects it to the gap in `RaftTrace.lean`.

## Background

`RaftTrace.lean` defines `RaftReachable` with a `step` constructor whose `hqc_preserved`
hypothesis asserts:
```
hqc_preserved : ∀ k e, isQuorumCommitted cs.voters cs.logs k e →
    ∀ w', cs'.logs w' k = cs.logs w' k
```
This says: *any entry quorum-committed in the old state is present in every voter's log
in the new state*.  This encodes the Leader Completeness property of Raft.

Leader Completeness (§5.4.1): *"If a log entry is committed in a given term, that entry
will be present in the logs of all leaders for all higher-numbered terms."*

The formal argument has two components:
1. **Quorum overlap** (LC1): the vote quorum and commit quorum share a voter.
2. **Log coverage** (LC_MAIN): if the winner's log covers every voter who voted
   for it, the winner has all committed entries.

The gap between "isUpToDate" and "log content matches" is filled by `CandidateLogCovers`,
a predicate that captures exactly what a concrete protocol would need to prove about the
AppendEntries + log matching invariant.

## This File Provides

1. **`VoteRecordConsistency`** — invariant that every recorded vote was cast via `voteGranted`.

2. **`CandidateLogCovers`** — the concrete protocol guarantee that a winning candidate's
   log agrees with every voter who voted for it, at every index where the voter has an entry.

3. **LC1** (`electionWinner_overlaps_commitQuorum`): vote quorum ∩ commit quorum ≠ ∅.

4. **LC2** (`electionWinner_shared_voter`): the shared voter voted for winner AND has the entry.

5. **LC3** (`leaderCompleteness`): winner has all committed entries, given `CandidateLogCovers`.

6. **LC4** (`leaderCompleteness_fullChain`): unique winner + has committed entries (uses RE5).

7. **LC5** (`wonInTerm_implies_isUpToDate`): voter who voted → winner was isUpToDate.

8. **LC5b** (`wonInTerm_voters_allUpToDate`): all voters who voted → winner was isUpToDate wrt each.

9. **LC6** (`hqc_preserved_from_leaderBroadcast`): concrete condition discharging `hqc_preserved`.

10. **LC7** (`candidateLog_of_logMatchingAndUpToDate`): conditional — LMI + VRC + HLogConsistency
    → CandidateLogCovers.

11. **LC8** (`leaderCompleteness_via_logMatching`): full leader completeness given all invariants.

## Remaining Gap

`HLogConsistency` (definition in this file) captures the final missing link: if the candidate
is isUpToDate relative to a voter who has entry `e` at index `k`, the candidate also has `e`
at `k`.  Proving `HLogConsistency` from concrete protocol transitions is the A4/A5 gap in
`TARGETS.md`.

## Theorem Index

| ID   | Name                                    | Status           | Description                                            |
|------|-----------------------------------------|------------------|--------------------------------------------------------|
| LC1  | `electionWinner_overlaps_commitQuorum`  | ✅ proved        | Vote quorum ∩ commit quorum shares a voter             |
| LC2  | `electionWinner_shared_voter`           | ✅ proved        | Shared voter voted for winner AND has committed entry  |
| LC3  | `leaderCompleteness`                    | ✅ proved        | Winner has committed entries (given CandLogCovers)     |
| LC4  | `leaderCompleteness_fullChain`          | ✅ proved        | Unique winner + has committed entries (uses RE5)       |
| LC5  | `wonInTerm_implies_isUpToDate`          | ✅ proved        | Voter who voted → winner was isUpToDate                |
| LC5b | `wonInTerm_voters_allUpToDate`          | ✅ proved        | All voters who voted → winner was isUpToDate wrt each  |
| LC6  | `hqc_preserved_from_leaderBroadcast`   | ✅ proved        | Discharge condition for hqc_preserved (no sorry)       |
| LC7  | `candidateLog_of_logMatchingAndUpToDate`| ✅ proved        | LMI + HLogConsistency → CandidateLogCovers             |
| LC8  | `leaderCompleteness_via_logMatching`    | ✅ proved        | Full LC given LMI + VRC + HLogConsistency              |

**Sorry count**: 0.  All theorems are conditional on explicit hypotheses; no sorry is used.
-/

namespace FVSquad.LeaderCompleteness

open FVSquad.RaftElection
open FVSquad.RaftSafety

/-! ## Key Definitions -/

/-- **VoteRecordConsistency** — every vote in the record was cast via `voteGranted`.

    This invariant says: if voter `w` voted for `cand` in `term`, then at the time of
    voting, `voteGranted (voterLog w) priorVote (candLastTerm cand) (candLastIndex cand) = true`
    for some prior vote and some candidate log coordinates.

    In a concrete Raft protocol, this is maintained by the vote-request handler:
    a node sets `record term w := some cand` only when `voteGranted` returns `true`. -/
def VoteRecordConsistency (record : VoteRecord) (voterLog : Nat → LogId)
    (candLastTerm : Nat → Nat) (candLastIndex : Nat → Nat) : Prop :=
  ∀ (t : Nat) (c : Nat) (w : Nat), record t w = some c →
    (voteGranted (voterLog w) (record t w) c (candLastTerm c) (candLastIndex c) : Bool) = true

/-- **CandidateLogCovers** — at every index where voter `w` (who voted for the winner) has
    an entry, the winner's log agrees with voter `w`'s log.

    This is the key bridge between the election model and log safety.  In a concrete
    Raft implementation, this follows from:
    1. **Log Matching**: if candidate's last entry is at least as recent/long as voter `w`'s,
       the candidate's log is an extension of `w`'s log (same entries up to `w`'s lastIndex).
    2. **No Truncation**: leaders never truncate committed entries (`maybe_append` panic).

    `CandidateLogCovers` encapsulates these two protocol-level invariants as a single
    hypothesis, making the dependency explicit. -/
def CandidateLogCovers (E : Type) (voters : List Nat) (record : VoteRecord)
    (term cand : Nat) (logs : VoterLogs E) (candLog : Nat → Option E) : Prop :=
  ∀ k e, ∀ w ∈ voters, record term w = some cand → logs w k = some e → candLog k = logs w k

/-- **HLogConsistency** — the missing protocol-level invariant connecting log freshness
    to log content agreement.

    If the candidate's log is at least as up-to-date as voter `w`'s log, and voter `w`
    has entry `e` at index `k`, then the candidate also has `e` at `k`.

    **Why this is not provable from `isUpToDate` alone**: `isUpToDate` compares
    `(lastTerm, lastIndex)` pairs lexicographically. Knowing the candidate's last entry
    is "newer" or "longer" tells us the candidate has a more recent or longer log, but
    does not directly tell us the candidate's log at specific index `k` equals the
    voter's log at `k`. This requires the Log Matching Property combined with knowledge
    of how the candidate's log was built via AppendEntries.

    **Proof obligation**: this is the A4/A5 gap in `TARGETS.md`. Discharging this requires
    a concrete model of AppendEntries transitions and log synchronisation. -/
def HLogConsistency (E : Type) (voterLog : Nat → LogId) (logs : VoterLogs E)
    (candLastTerm : Nat → Nat) (candLastIndex : Nat → Nat) (candLog : Nat → Option E) : Prop :=
  ∀ cand w k e,
    isUpToDate (voterLog w) (candLastTerm cand) (candLastIndex cand) = true →
    logs w k = some e →
    k ≤ (voterLog w).index →
    candLog k = logs w k

/-! ## LC1: Vote quorum overlaps commit quorum -/

/-- **LC1** — The election vote quorum and the commit quorum share at least one voter.

    If candidate `cand` wins in `term` (a majority quorum voted for it) and entry `e`
    is quorum-committed at index `k`, then there exists a voter `w` in both quorums.

    **Proof**: direct application of `quorum_intersection_mem` (HQ20).  Both `wonInTerm`
    and `isQuorumCommitted` use `hasQuorum` over the same voter list, so quorum
    intersection applies immediately.

    **Significance**: This is the foundational step of the Raft leader completeness
    argument (§5.4.2) — the proof that any two majorities share a member. -/
theorem electionWinner_overlaps_commitQuorum [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (term cand : Nat)
    (logs : VoterLogs E) (k : Nat) (e : E)
    (hwin    : wonInTerm (hd :: tl) record term cand = true)
    (hcommit : isQuorumCommitted (hd :: tl) logs k e) :
    ∃ w ∈ (hd :: tl), record term w = some cand ∧ logs w k = some e := by
  simp only [wonInTerm] at hwin
  unfold isQuorumCommitted at hcommit
  obtain ⟨w, hmem, hv1, hv2⟩ :=
    quorum_intersection_mem hd tl
      (fun voter => decide (record term voter = some cand))
      (fun voter => decide (logs voter k = some e))
      hwin hcommit
  exact ⟨w, hmem,
    by simp only [decide_eq_true_eq] at hv1; exact hv1,
    by simp only [decide_eq_true_eq] at hv2; exact hv2⟩

/-! ## LC2: Shared voter voted for winner and has committed entry -/

/-- **LC2** — The voter shared between the vote quorum and commit quorum both voted
    for the election winner AND has the committed entry in their log.

    This is a direct corollary of LC1, restating the conclusion more explicitly. -/
theorem electionWinner_shared_voter [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (term cand : Nat)
    (logs : VoterLogs E) (k : Nat) (e : E)
    (hwin    : wonInTerm (hd :: tl) record term cand = true)
    (hcommit : isQuorumCommitted (hd :: tl) logs k e) :
    ∃ w ∈ (hd :: tl),
      record term w = some cand  -- w voted for cand
      ∧ logs w k = some e        -- w has e at index k
      :=
  electionWinner_overlaps_commitQuorum hd tl record term cand logs k e hwin hcommit

/-! ## LC3: Leader completeness — main theorem -/

/-- **LC3 — Leader Completeness** (main theorem): if candidate `cand` wins the election
    in `term` and `CandidateLogCovers` holds, then the winner has all quorum-committed entries.

    **Proof**:
    1. By LC1, get shared voter `w` with `record term w = some cand` and `logs w k = some e`.
    2. By `CandidateLogCovers`, `candLog k = logs w k`.
    3. Therefore `candLog k = some e`.

    **Note on `CandidateLogCovers`**: this hypothesis is what remains to be discharged
    from a concrete protocol model.  See `TARGETS.md §A4` and LC7 below. -/
theorem leaderCompleteness [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (term cand : Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (k : Nat) (e : E)
    (hwin    : wonInTerm (hd :: tl) record term cand = true)
    (hcommit : isQuorumCommitted (hd :: tl) logs k e)
    (hcovers : CandidateLogCovers E (hd :: tl) record term cand logs candLog) :
    candLog k = some e := by
  obtain ⟨w, hmem, hvote, hlog⟩ :=
    electionWinner_overlaps_commitQuorum hd tl record term cand logs k e hwin hcommit
  have hcand : candLog k = logs w k := hcovers k e w hmem hvote hlog
  rw [hcand]; exact hlog

/-! ## LC4: Full chain — unique winner with committed entries -/

/-- **LC4** — Composition with election safety (RE5): the unique election winner has
    all committed entries.

    If both `c1` and `c2` win in `term`, they are equal (by RE5/`electionSafety`).
    If additionally `CandidateLogCovers` holds for `c1`, then `c1`'s log has all
    committed entries. -/
theorem leaderCompleteness_fullChain [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (term c1 c2 : Nat)
    (logs : VoterLogs E) (cand1Log : Nat → Option E) (k : Nat) (e : E)
    (hw1     : wonInTerm (hd :: tl) record term c1 = true)
    (hw2     : wonInTerm (hd :: tl) record term c2 = true)
    (hcommit : isQuorumCommitted (hd :: tl) logs k e)
    (hcovers : CandidateLogCovers E (hd :: tl) record term c1 logs cand1Log) :
    cand1Log k = some e ∧ c1 = c2 :=
  ⟨leaderCompleteness hd tl record term c1 logs cand1Log k e hw1 hcommit hcovers,
   electionSafety hd tl record term c1 c2 hw1 hw2⟩

/-! ## LC5: Vote record consistency implies isUpToDate -/

/-- **LC5** — If `VoteRecordConsistency` holds and voter `w` voted for `cand` in `term`,
    then `isUpToDate (voterLog w) (candLastTerm cand) (candLastIndex cand) = true`.

    This is the formal bridge between "a vote was cast" and "the winner was at least as
    log-fresh as the voter" — the Raft §5.4.1 vote-granting condition. -/
theorem wonInTerm_implies_isUpToDate
    (record : VoteRecord) (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (hconsist : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (term cand w : Nat)
    (hvote : record term w = some cand) :
    isUpToDate (voterLog w) (candLastTerm cand) (candLastIndex cand) = true :=
  voteGranted_isUpToDate (voterLog w) (record term w) cand (candLastTerm cand) (candLastIndex cand)
    (hconsist term cand w hvote)

/-- **LC5b** — If VoteRecordConsistency holds and candidate `cand` won in `term`, then
    every voter `w` who voted for `cand` had the winner as at least as log-fresh. -/
theorem wonInTerm_voters_allUpToDate
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (hconsist : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (term cand : Nat)
    (hwin : wonInTerm (hd :: tl) record term cand = true) :
    ∀ w ∈ (hd :: tl), record term w = some cand →
      isUpToDate (voterLog w) (candLastTerm cand) (candLastIndex cand) = true := by
  intro w _ hvote
  exact wonInTerm_implies_isUpToDate record voterLog candLastTerm candLastIndex
          hconsist term cand w hvote

/-! ## LC6: Discharge condition for hqc_preserved -/

/-- **LC6** — `hqc_preserved` holds if (a) the leader has all committed entries, and
    (b) AppendEntries broadcasts the leader's committed entries to ALL voters.

    The `hqc_preserved` condition in `RaftReachable.step` says:
    ```
    ∀ k e, isQuorumCommitted cs.voters cs.logs k e →
        isQuorumCommitted cs'.voters cs'.logs k e
    ```
    (In fact, the RaftTrace version requires `∀ w', cs'.logs w' k = cs.logs w' k`, which
    is even stronger — it requires ALL logs to have the entry, not just a quorum.)

    This theorem proves the weaker (but still useful) version: `isQuorumCommitted` is
    preserved across the transition, given leader completeness + broadcast.

    **Proof**:
    1. By LC3, the leader has `e` at `k` (`logs leader k = some e`).
    2. By `happend`, all voters in `cs'` have `logs' w k = logs leader k = some e`.
    3. The predicate `fun v => decide (logs' v k = some e)` is `true` for ALL voters.
    4. By `hasQuorum_true_of_all_in`, `isQuorumCommitted` holds in the new state. -/
theorem hqc_preserved_from_leaderBroadcast [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (term leader : Nat)
    (logs logs' : VoterLogs E)
    (hwin    : wonInTerm (hd :: tl) record term leader = true)
    (hcovers : CandidateLogCovers E (hd :: tl) record term leader logs (logs leader))
    (happend : ∀ k e, isQuorumCommitted (hd :: tl) logs k e →
                ∀ w', logs' w' k = logs leader k) :
    ∀ k e, isQuorumCommitted (hd :: tl) logs k e →
      isQuorumCommitted (hd :: tl) logs' k e := by
  intro k e hcommit
  have hleader_has : logs leader k = some e :=
    leaderCompleteness hd tl record term leader logs (logs leader) k e hwin hcommit hcovers
  unfold isQuorumCommitted
  apply hasQuorum_true_of_all_in
  intro w _
  simp only [decide_eq_true_eq]
  rw [happend k e hcommit w]; exact hleader_has

/-! ## LC7: Connecting isUpToDate to CandidateLogCovers -/

/-- **LC7** — If `VoteRecordConsistency` and `HLogConsistency` both hold, then
    `CandidateLogCovers` follows.

    **Proof**:
    1. Voter `w` voted for `cand` → by VRC, `voteGranted` was called → `isUpToDate` holds.
    2. Voter `w` has `e` at `k` in their log.
    3. By `HLogConsistency`, `candLog k = logs w k`.

    **What remains**: proving `HLogConsistency` from a concrete Raft protocol model.
    This requires showing that AppendEntries + `LogMatchingInvariantFor` ensures the
    leader's log agrees with any voter who voted for it at all committed indices. -/
theorem candidateLog_of_logMatchingAndUpToDate
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (term cand : Nat)
    (hconsist  : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (hlogcons  : HLogConsistency E voterLog logs candLastTerm candLastIndex candLog)
    (hvoter_idx : ∀ w k e, w ∈ (hd :: tl) → logs w k = some e → k ≤ (voterLog w).index) :
    CandidateLogCovers E (hd :: tl) record term cand logs candLog := by
  intro k e w hmem hvote hlog
  have hfresh := wonInTerm_implies_isUpToDate record voterLog candLastTerm candLastIndex
                   hconsist term cand w hvote
  have hkle   := hvoter_idx w k e hmem hlog
  exact hlogcons cand w k e hfresh hlog hkle

/-! ## LC8: Full leader completeness given all three invariants -/

/-- **LC8** — Full leader completeness: if `VoteRecordConsistency`, `HLogConsistency`,
    and the voter-index domination condition all hold, then any election winner has all
    quorum-committed entries.

    **Proof**: LC7 gives `CandidateLogCovers`; then LC3 concludes.

    **What this proves**: the complete chain from "candidate won election via Raft
    vote-granting condition" to "candidate has all quorum-certified log entries",
    conditional on `HLogConsistency` (the A4/A5 gap). -/
theorem leaderCompleteness_via_logMatching [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (voterLog : Nat → LogId)
    (candLastTerm candLastIndex : Nat → Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (term cand : Nat) (k : Nat) (e : E)
    (hwin     : wonInTerm (hd :: tl) record term cand = true)
    (hcommit  : isQuorumCommitted (hd :: tl) logs k e)
    (hconsist : VoteRecordConsistency record voterLog candLastTerm candLastIndex)
    (hlogcons : HLogConsistency E voterLog logs candLastTerm candLastIndex candLog)
    (hvoter_idx : ∀ w k e, w ∈ (hd :: tl) → logs w k = some e → k ≤ (voterLog w).index) :
    candLog k = some e :=
  leaderCompleteness hd tl record term cand logs candLog k e hwin hcommit
    (candidateLog_of_logMatchingAndUpToDate hd tl record voterLog candLastTerm candLastIndex
      logs candLog term cand hconsist hlogcons hvoter_idx)

/-! ## Connection to RSS5 (raft_leader_completeness_via_witness) -/

/-- The winner's log covers the commit quorum, so `raft_leader_completeness_via_witness`
    (RSS5) applies directly.  This re-derives LC3 via the `hwitness` pattern for a
    direct connection to the `RaftSafety` framework. -/
theorem leaderCompleteness_via_rss5 [DecidableEq E]
    (hd : Nat) (tl : List Nat) (record : VoteRecord) (term cand : Nat)
    (logs : VoterLogs E) (candLog : Nat → Option E) (k : Nat) (e : E)
    (hwin    : wonInTerm (hd :: tl) record term cand = true)
    (hcommit : isQuorumCommitted (hd :: tl) logs k e)
    (hcovers : CandidateLogCovers E (hd :: tl) record term cand logs candLog) :
    candLog k = some e := by
  obtain ⟨w, hmem, hvote, hlog⟩ :=
    electionWinner_overlaps_commitQuorum hd tl record term cand logs k e hwin hcommit
  have hcand_eq : candLog k = logs w k := hcovers k e w hmem hvote hlog
  exact raft_leader_completeness_via_witness hd tl logs candLog k e hcommit
    ⟨w, hmem, hlog, hcand_eq⟩

/-! ## Evaluation sanity checks -/

-- Majority quorum: in a 3-voter cluster, voters {1,2} form a majority → candidate 5 wins.
#eval wonInTerm [1, 2, 3]
  (fun t v => if t == 1 && (v == 1 || v == 2) then some 5 else none) 1 5
-- Expected: true

-- Non-winner: candidate 6 has no votes → does not win.
#eval wonInTerm [1, 2, 3]
  (fun t v => if t == 1 && (v == 1 || v == 2) then some 5 else none) 1 6
-- Expected: false

-- ElectionSafety: only one winner per term (5 ≠ 6 → only one can have a majority).
#eval wonInTerm [1, 2, 3]
  (fun t v => if t == 1 then (if v == 1 || v == 2 then some 5 else some 6) else none) 1 5
-- Expected: true (voters 1,2 voted for 5)
#eval wonInTerm [1, 2, 3]
  (fun t v => if t == 1 then (if v == 1 || v == 2 then some 5 else some 6) else none) 1 6
-- Expected: false (only voter 3 voted for 6 — not a majority)

end FVSquad.LeaderCompleteness
