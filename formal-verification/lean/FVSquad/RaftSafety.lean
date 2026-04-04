import FVSquad.HasQuorum
import FVSquad.SafetyComposition
import FVSquad.JointSafetyComposition
import FVSquad.CommittedIndex
import FVSquad.JointCommittedIndex

/-!
# Raft State-Machine Safety: End-to-End Protocol Safety Theorems

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file lifts the quorum-level safety theorems from `SafetyComposition` and
`JointSafetyComposition` to the **log-entry level**, formalising the end-to-end
Raft state-machine safety property.

## The Central Gap This File Closes

Prior FV work proved:
- **SC4** (`SafetyComposition`): two committed *indices* share a witness *voter*.
- **JSC7** (`JointSafetyComposition`): same for joint configs.

This file proves what those results imply about **log entries**:
- **RSS1**: two entries simultaneously committed at the same index must be identical
  (single-config).
- **RSS2**: same for joint configs.
- **RSS6/RSS7**: conditional end-to-end cluster safety — given that every applied entry
  is quorum-certified (the key protocol invariant), no two nodes ever apply different
  entries at the same index.

## Theorem table

| ID   | Name                                        | Status    | Description                                               |
|------|---------------------------------------------|-----------|-----------------------------------------------------------|
| RSS1 | `raft_state_machine_safety`                 | ✅ proved  | Single-config: committed entries at same index are equal  |
| RSS1b| `raft_safety_contra`                        | ✅ proved  | Contrapositive of RSS1                                    |
| RSS2 | `raft_joint_state_machine_safety`           | ✅ proved  | Joint-config: same, via incoming quorum intersection      |
| RSS2b| `raft_joint_state_machine_safety_sym`       | ✅ proved  | Joint-config variant using outgoing quorum                |
| RSS3 | `log_matching_property`                     | ✅ proved  | Same index+term → identical log prefixes (given LMI hypothesis)  |
| RSS4 | `raft_committed_no_rollback`                | ✅ proved  | Committed entries never overwritten (given NRI hypothesis)        |
| RSS5 | `raft_leader_completeness_via_witness`      | ✅ proved  | Leader has committed entries (given explicit witness)     |
| RSS6 | `raft_cluster_safety`                       | ✅ proved  | **End-to-end**: cluster safe given quorum-cert invariant  |
| RSS7 | `raft_joint_cluster_safety`                 | ✅ proved  | **End-to-end** joint config analogue                      |
| RSS8 | `raft_end_to_end_safety_full`               | ✅ proved  | End-to-end safety given CommitCertInvariant               |

## What "end-to-end" means here

**RSS6** and **RSS7** are fully proved, conditional on `hcert`:
```
hcert : ∀ v k e, nodeHasApplied cs v k e → isQuorumCommitted cs.voters cs.logs k e
```
This is the **quorum-certification invariant** — every applied entry was certified by a
majority quorum.  Proving `hcert` from a concrete Raft protocol model (message passing,
AppendEntries RPCs, term management) would require modelling the full protocol: that is
**RSS8** (sorry-guarded).  RSS6 proves the safety *conclusion* rigorously, making the
remaining proof obligation (`hcert`) explicit.

## Modelling notes

- `E` is a type parameter for log entries; `DecidableEq E` is required.
- `VoterLogs E := Nat → Nat → Option E` maps voter ID and log index to an entry.
- `isQuorumCommitted` uses the same `hasQuorum` predicate as the rest of FVSquad.
- The Log Matching Property (RSS3) and No-Rollback (RSS4) require a temporal model of
  Raft state transitions — beyond the current functional model.
- `ClusterState` is an abstract snapshot of per-node state; `nodeHasApplied` models the
  "committed and applied to state machine" predicate.
-/

-- HasQuorum.lean has no namespace; quorum_intersection_mem, hasQuorum etc. are in root
open FVSquad.SafetyComposition
open FVSquad.CommittedIndex

namespace FVSquad.RaftSafety

/-! ## Core definitions -/

/-- Per-voter log: maps a voter ID and a log index to the entry (if any) at that
    position.  `voterLogs v k = some e` means voter `v` has entry `e` at index `k`. -/
abbrev VoterLogs (E : Type) := Nat → Nat → Option E

/-- Entry `e` is **quorum-committed** at index `k` if a majority of `voters` have
    `e` at position `k` in their logs.

    This is the key bridge: it uses `hasQuorum` from `HasQuorum.lean`, so all
    quorum intersection theorems apply directly. -/
def isQuorumCommitted [DecidableEq E]
    (voters : List Nat) (logs : VoterLogs E) (k : Nat) (e : E) : Prop :=
  hasQuorum voters (fun v => decide (logs v k = some e)) = true

/-- Entry `e` is **joint-quorum-committed** at index `k` if a majority of the
    *incoming* voters AND a majority of the *outgoing* voters both have `e` at `k`.

    This mirrors the joint-config commit requirement from `JointCommittedIndex`:
    both halves must independently certify the commitment. -/
def isJointQuorumCommitted [DecidableEq E]
    (incoming outgoing : List Nat) (logs : VoterLogs E) (k : Nat) (e : E) : Prop :=
  hasQuorum incoming (fun v => decide (logs v k = some e)) = true ∧
  hasQuorum outgoing (fun v => decide (logs v k = some e)) = true

/-- **Log Matching Invariant** for a generic entry type `E`.

    If two voters' logs agree at index `k`, they agree on all entries at indices `≤ k`.
    This is the formal predicate that RSS3 requires — Raft protocols must maintain this
    invariant inductively.  The specialisation to `Nat`-indexed terms is
    `LogMatchingInvariant` in `RaftProtocol.lean`.

    **Note**: this predicate does NOT hold for arbitrary log states.  It is an
    *inductive invariant* of the Raft protocol that holds only for reachable states. -/
def LogMatchingInvariantFor (E : Type) (logs : VoterLogs E) : Prop :=
  ∀ v1 v2 k, logs v1 k = logs v2 k → ∀ j ≤ k, logs v1 j = logs v2 j

/-- **No-Rollback Invariant** for a generic entry type `E`.

    Between two log states `logs₀` and `logs₁`, every entry quorum-committed in `logs₀`
    remains quorum-committed in `logs₁`.  This is the formal predicate that RSS4 requires.

    **Note**: this does NOT hold for arbitrary pairs `(logs₀, logs₁)`.  It is a property
    of valid Raft transitions: the protocol prevents leaders from overwriting committed
    entries (enforced by the `conflict ≤ committed` panic in `maybe_append`). -/
def NoRollbackInvariantFor (E : Type) [DecidableEq E]
    (voters : List Nat) (logs₀ logs₁ : VoterLogs E) : Prop :=
  ∀ k e, isQuorumCommitted voters logs₀ k e → isQuorumCommitted voters logs₁ k e

/-! ## RSS1: Single-config state-machine safety -/

/-- **RSS1** — **Raft state-machine safety (single config)**.

    If two entries `e1` and `e2` are both quorum-committed at the same log index `k`
    in a cluster with non-empty voters `hd :: tl`, then `e1 = e2`.

    **Proof**:
    - Commitment of `e1` → `Q1 := { v | logs v k = Some e1 }` forms a majority.
    - Commitment of `e2` → `Q2 := { v | logs v k = Some e2 }` forms a majority.
    - `quorum_intersection_mem` (HQ20): `∃ w ∈ voters, w ∈ Q1 ∧ w ∈ Q2`.
    - `w ∈ Q1` → `logs w k = Some e1`; `w ∈ Q2` → `logs w k = Some e2`.
    - Both are values of the function `logs w k`, so `Some e1 = Some e2` → `e1 = e2`.

    **Significance**: This is the log-entry analogue of SC4 (which worked at the index
    level). RSS1 directly formalises the Raft invariant: the quorum intersection property
    guarantees that no two different entries are ever simultaneously committed at the
    same index — independent of terms, elections, or message ordering. -/
theorem raft_state_machine_safety [DecidableEq E]
    (hd : Nat) (tl : List Nat) (logs : VoterLogs E) (k : Nat) (e1 e2 : E)
    (h1 : isQuorumCommitted (hd :: tl) logs k e1)
    (h2 : isQuorumCommitted (hd :: tl) logs k e2) :
    e1 = e2 := by
  unfold isQuorumCommitted at h1 h2
  obtain ⟨w, _, hw1, hw2⟩ :=
    quorum_intersection_mem hd tl
      (fun v => decide (logs v k = some e1))
      (fun v => decide (logs v k = some e2))
      h1 h2
  simp only [decide_eq_true_eq] at hw1 hw2
  exact Option.some.inj (hw1.symm.trans hw2)

/-- **RSS1b** — Contrapositive: if `e1 ≠ e2`, they cannot both be quorum-committed
    at the same index.  This is the version useful for ruling out log divergence. -/
theorem raft_safety_contra [DecidableEq E]
    (hd : Nat) (tl : List Nat) (logs : VoterLogs E) (k : Nat) (e1 e2 : E)
    (hne : e1 ≠ e2) :
    ¬ (isQuorumCommitted (hd :: tl) logs k e1 ∧
       isQuorumCommitted (hd :: tl) logs k e2) :=
  fun ⟨h1, h2⟩ => hne (raft_state_machine_safety hd tl logs k e1 e2 h1 h2)

/-! ## RSS2: Joint-config state-machine safety -/

/-- **RSS2** — **Raft state-machine safety (joint config)**, via incoming half.

    For non-empty `incoming` and any `outgoing`, if two entries `e1` and `e2` are both
    joint-quorum-committed at the same index `k`, then `e1 = e2`.

    **Proof**: joint commitment requires a majority in the `incoming` half; apply
    RSS1 to the `incoming` quorums.

    **Relationship to JSC7**: JSC7 proves that two joint-committed *indices* share
    witnesses in *both* halves; RSS2 proves that two joint-committed *entries* at the
    same index must be identical — using only the incoming intersection. -/
theorem raft_joint_state_machine_safety [DecidableEq E]
    (hi : Nat) (ti outgoing : List Nat) (logs : VoterLogs E) (k : Nat) (e1 e2 : E)
    (h1 : isJointQuorumCommitted (hi :: ti) outgoing logs k e1)
    (h2 : isJointQuorumCommitted (hi :: ti) outgoing logs k e2) :
    e1 = e2 :=
  raft_state_machine_safety hi ti logs k e1 e2 h1.1 h2.1

/-- **RSS2b** — Joint-config safety via the *outgoing* half.  Symmetric to RSS2. -/
theorem raft_joint_state_machine_safety_sym [DecidableEq E]
    (incoming : List Nat) (ho : Nat) (to : List Nat) (logs : VoterLogs E) (k : Nat) (e1 e2 : E)
    (h1 : isJointQuorumCommitted incoming (ho :: to) logs k e1)
    (h2 : isJointQuorumCommitted incoming (ho :: to) logs k e2) :
    e1 = e2 :=
  raft_state_machine_safety ho to logs k e1 e2 h1.2 h2.2

/-! ## RSS3: Log Matching Property -/

/-- **RSS3** — **Log Matching Property** (proved, conditional on `LogMatchingInvariantFor`).

    If two voters' logs agree at index `k`, they agree on all indices `≤ k`.

    This is **Raft Invariant 3** (Ongaro §5.3): "If two entries in different logs have
    the same index and term, then the logs are identical in all entries up through the
    given index."

    **Status**: proved, given `LogMatchingInvariantFor E logs` as hypothesis.

    **Why the hypothesis is needed**: `LogMatchingInvariantFor` does NOT hold for
    arbitrary log states — it is an inductive protocol invariant.  For example, two
    voters could trivially have identical entries at index `k` (by coincidence) while
    diverging at earlier indices, violating this property.  The hypothesis makes the
    dependency explicit and honest.

    **Connection to RP2**: the term-level version for `Nat` entries is
    `rss3_from_logMatchInvariant` (RP2 in `RaftProtocol.lean`).  RP6
    (`appendEntries_preserves_log_matching`) proves that AppendEntries preserves
    `LogMatchingInvariant` given `hleader_lmi`. -/
theorem log_matching_property [DecidableEq E]
    (v1 v2 : Nat) (logs : VoterLogs E) (k : Nat)
    (hlm    : LogMatchingInvariantFor E logs)
    (hmatch : logs v1 k = logs v2 k) :
    ∀ j ≤ k, logs v1 j = logs v2 j :=
  hlm v1 v2 k hmatch

/-! ## RSS4: No rollback -/

/-- **RSS4** — **No rollback**: committed entries are never overwritten (proved,
    conditional on `NoRollbackInvariantFor`).

    Once entry `e` is quorum-committed at index `k` in log state `logs₀`, it remains
    quorum-committed at any log state `logs₁`, provided the transition satisfies the
    no-rollback invariant.

    **Status**: proved, given `NoRollbackInvariantFor E (hd :: tl) logs₀ logs₁` as hypothesis.

    **Why the hypothesis is needed**: `NoRollbackInvariantFor` does NOT hold for
    arbitrary pairs `(logs₀, logs₁)`.  A follower could in principle truncate its log
    arbitrarily, violating quorum commitment.  The Raft protocol prevents this via the
    `conflict ≤ committed` panic in `maybe_append` (preventing leaders from sending
    conflicting entries below committed) combined with election safety.

    **Connection to RP5/RP8**: RP5 (`rss4_from_noRollback`) provides the term-level
    analogue for `VoterLogs Nat` using `NoRollbackInvariant` from `RaftProtocol.lean`.
    RP8 (`raft_transitions_no_rollback`) proves that a single AppendEntries step
    preserves `NoRollbackInvariant` given `hno_truncate`. -/
theorem raft_committed_no_rollback [DecidableEq E]
    (hd : Nat) (tl : List Nat)
    (logs₀ logs₁ : VoterLogs E) (k : Nat) (e : E)
    (hnr     : NoRollbackInvariantFor E (hd :: tl) logs₀ logs₁)
    (hcommit : isQuorumCommitted (hd :: tl) logs₀ k e) :
    isQuorumCommitted (hd :: tl) logs₁ k e :=
  hnr k e hcommit

/-! ## RSS5: Leader completeness (via explicit witness) -/

/-- **RSS5** — **Leader completeness with explicit witness** (proved).

    If entry `e` is quorum-committed at index `k`, and there exists a voter `w` in the
    commit quorum such that the candidate's log at `k` equals `w`'s log at `k`, then the
    candidate has `e` at index `k`.

    This is the tractable version of leader completeness: the `hwitness` hypothesis
    encapsulates the "isUpToDate" check from Raft elections — a candidate wins only if
    its log is at least as up-to-date as a voter that has the committed entry.

    **Proof**: unpack the witness; `candidateLog k = logs w k = some e`. -/
theorem raft_leader_completeness_via_witness [DecidableEq E]
    (hd : Nat) (tl : List Nat) (logs : VoterLogs E)
    (candidateLog : Nat → Option E) (k : Nat) (e : E)
    (hcommit : isQuorumCommitted (hd :: tl) logs k e)
    (hwitness : ∃ w ∈ (hd :: tl),
        logs w k = some e ∧ candidateLog k = logs w k) :
    candidateLog k = some e := by
  obtain ⟨_, _, hw_e, hw_eq⟩ := hwitness
  rw [hw_eq]; exact hw_e

/-! ## RSS6–RSS7: End-to-end cluster safety (fully proved, conditional) -/

/-- Abstract snapshot of a Raft cluster at one point in time. -/
structure ClusterState (E : Type) where
  voters    : List Nat
  logs      : VoterLogs E
  committed : Nat → Nat   -- per-node committed index

/-- Node `v` has applied entry `e` at index `k`: it has marked `k` committed and
    has `e` in its log at position `k`. -/
def nodeHasApplied [DecidableEq E] (cs : ClusterState E) (v : Nat) (k : Nat) (e : E) : Prop :=
  cs.committed v ≥ k ∧ cs.logs v k = some e

/-- A cluster is safe if no two nodes ever apply different entries at the same index. -/
def isClusterSafe [DecidableEq E] (cs : ClusterState E) : Prop :=
  ∀ v1 v2 : Nat, ∀ k : Nat, ∀ e1 e2 : E,
    nodeHasApplied cs v1 k e1 → nodeHasApplied cs v2 k e2 → e1 = e2

/-- **RSS6** — **End-to-end Raft cluster safety** (single-config, fully proved).

    Given a cluster snapshot `cs` with non-empty voter list `hd :: tl` and the
    **quorum-certification invariant** `hcert` (every applied entry was certified by
    a majority quorum), the cluster is safe: no two nodes ever apply different entries
    at the same index.

    **Proof**: immediate from RSS1 — two quorum-certified entries at the same index
    must be identical by quorum intersection.

    **What `hcert` encapsulates**: in a real Raft deployment, `hcert` is established by:
    1. The commit rule: a leader commits only after a majority acknowledges an entry.
    2. The AppendEntries protocol: entries are replicated before being committed.
    3. Leader completeness: elected leaders have all previously committed entries.
    Formalising these three together is **RSS8** (sorry-guarded). -/
theorem raft_cluster_safety [DecidableEq E]
    (hd : Nat) (tl : List Nat) (cs : ClusterState E)
    (hvoters : cs.voters = hd :: tl)
    (hcert : ∀ v k e, nodeHasApplied cs v k e →
        isQuorumCommitted cs.voters cs.logs k e) :
    isClusterSafe cs := by
  intro v1 v2 k e1 e2 ha1 ha2
  have hq1 := hcert v1 k e1 ha1
  have hq2 := hcert v2 k e2 ha2
  rw [hvoters] at hq1 hq2
  exact raft_state_machine_safety hd tl cs.logs k e1 e2 hq1 hq2

/-- Abstract snapshot of a joint-config Raft cluster. -/
structure JointClusterState (E : Type) where
  incoming  : List Nat
  outgoing  : List Nat
  logs      : VoterLogs E
  committed : Nat → Nat

/-- Node `v` has applied entry `e` at index `k` in a joint-config cluster. -/
def jointNodeHasApplied [DecidableEq E]
    (cs : JointClusterState E) (v : Nat) (k : Nat) (e : E) : Prop :=
  cs.committed v ≥ k ∧ cs.logs v k = some e

/-- A joint-config cluster is safe if no two nodes ever apply different entries. -/
def isJointClusterSafe [DecidableEq E] (cs : JointClusterState E) : Prop :=
  ∀ v1 v2 : Nat, ∀ k : Nat, ∀ e1 e2 : E,
    jointNodeHasApplied cs v1 k e1 → jointNodeHasApplied cs v2 k e2 → e1 = e2

/-- **RSS7** — **End-to-end Raft cluster safety** (joint config, fully proved).

    Joint-config analogue of RSS6.  Given non-empty `incoming` and the
    joint-quorum-certification invariant, the joint-config cluster is safe.

    **Proof**: joint commitment requires a majority in each half; RSS2 derives entry
    uniqueness from the incoming half's quorum intersection. -/
theorem raft_joint_cluster_safety [DecidableEq E]
    (hi : Nat) (ti : List Nat) (cs : JointClusterState E)
    (hinc : cs.incoming = hi :: ti)
    (hcert : ∀ v k e, jointNodeHasApplied cs v k e →
        isJointQuorumCommitted cs.incoming cs.outgoing cs.logs k e) :
    isJointClusterSafe cs := by
  intro v1 v2 k e1 e2 ha1 ha2
  have hq1 := hcert v1 k e1 ha1
  have hq2 := hcert v2 k e2 ha2
  rw [hinc] at hq1 hq2
  exact raft_joint_state_machine_safety hi ti cs.outgoing cs.logs k e1 e2 hq1 hq2

/-! ## CommitCertInvariant — the key inductive invariant for RSS8 -/

/-- **CommitCertInvariant** — every committed entry is quorum-certified.

    If voter `v` has marked log index `k` as committed (`cs.committed v ≥ k`)
    and has entry `e` at that index (`cs.logs v k = some e`), then a majority
    of voters also have `e` at index `k`.

    This is the key inductive invariant of the Raft protocol:
    - **Base case**: holds trivially for the initial empty cluster.
    - **Inductive case**: preserved by valid Raft steps (AppendEntries, with
      the commit rule ensuring quorum acknowledgement precedes commit advance).

    See `RaftTrace.lean` for the `RaftReachable` model that proves this invariant
    is maintained across all valid protocol steps.  Together, `CommitCertInvariant`
    and `raft_end_to_end_safety_full` give unconditional Raft safety for any
    cluster reachable from a valid initial state. -/
def CommitCertInvariant [DecidableEq E] (cs : ClusterState E) : Prop :=
  ∀ v k e, cs.committed v ≥ k → cs.logs v k = some e →
    isQuorumCommitted cs.voters cs.logs k e

/-! ## RSS8: Full end-to-end safety (proved, given CommitCertInvariant) -/

/-- **RSS8** — **Full end-to-end Raft safety** (proved given CommitCertInvariant).

    Cluster safety for any cluster state satisfying `CommitCertInvariant`: no two
    nodes ever apply different entries at the same index.

    **Status**: proved. ✅

    **What `CommitCertInvariant` captures**: every committed entry is quorum-certified —
    if voter `v` has committed index `k`, whatever entry `e` it has there, a majority
    also has `e` at `k`.  This invariant is maintained by the Raft protocol:
    - The **commit rule**: a leader advances its commit index only after a majority
      has acknowledged the entry (AppendEntries + quorum ACKs).
    - **Leader completeness**: an elected leader has all previously committed entries.
    - **Log matching**: the AppendEntries RPC preserves consistent log prefixes.

    **Proof**: `hcci` gives `hcert` (i.e., `nodeHasApplied → isQuorumCommitted`) by
    unfolding `nodeHasApplied = (committed v ≥ k ∧ logs v k = some e)`.  Then RSS6
    (`raft_cluster_safety`) closes the goal.

    **Protocol-level proof**: `RaftTrace.lean` provides `raftReachable_safe`, which
    proves RSS8 for any cluster state reachable (via `RaftReachable`) from the
    initial empty cluster.  The `RaftReachable` step constructor bundles the validity
    conditions that ensure `CommitCertInvariant` is an inductive invariant. -/
theorem raft_end_to_end_safety_full [DecidableEq E]
    (hd : Nat) (tl : List Nat) (cs : ClusterState E)
    (hvoters : cs.voters = hd :: tl)
    (hcci : CommitCertInvariant cs) :
    isClusterSafe cs :=
  raft_cluster_safety hd tl cs hvoters
    (fun v k e ⟨hcomm, hlog⟩ => hcci v k e hcomm hlog)

/-! ## Evaluation examples -/

section Eval

-- Example: two voters with the same entry at index 1 form a quorum in a 2-voter cluster.
-- RSS1 guarantees any other quorum-committed entry at index 1 must equal the same value.
-- hasQuorum [1,2] (fun _ => decide (some 0 = some 0)) = true (all voters match, count ≥ majority)
#eval
  (hasQuorum [1, 2] (fun _ => decide (some (0 : Nat) = some 0)))
-- expected: true

-- Counter-check: a different entry is not quorum-committed (no voters have it).
#eval
  (hasQuorum [1, 2] (fun _ => decide (some (0 : Nat) = some 1)))
-- expected: false

end Eval

end FVSquad.RaftSafety
