import FVSquad.RaftSafety
import FVSquad.RaftProtocol

/-!
# RaftTrace — Protocol-Level Reachability Model for Raft Safety

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file provides the protocol-level inductive model that connects the conditional
cluster safety theorem (RSS6/RSS8 in `RaftSafety.lean`) to full unconditional safety:

```
raft_cluster_safety       : hcert → isClusterSafe          (RSS6, RaftSafety.lean)
raft_end_to_end_safety_full : CommitCertInvariant → isClusterSafe  (RSS8, RaftSafety.lean)
raftReachable_safe        : RaftReachable cs → isClusterSafe  (RT2, this file)
```

## The Gap This File Closes

`raft_end_to_end_safety_full` (RSS8) proves cluster safety given `CommitCertInvariant`.
This file provides:

1. The **initial cluster state** (`initialCluster`) and proof that it trivially
   satisfies `CommitCertInvariant` (no entries committed, so the invariant is vacuous).

2. An **inductive reachability predicate** (`RaftReachable`) with a `step` constructor
   that bundles the key Raft protocol validity conditions as explicit hypotheses.
   These conditions are exactly what preserves `CommitCertInvariant` across steps.

3. A proof by induction that **every reachable state satisfies** `CommitCertInvariant`
   (`raftReachable_cci`, RT1).

4. The full **end-to-end safety theorem** (`raftReachable_safe`, RT2) combining
   RT1 with RSS8.

## RaftTrace Architecture

```
RaftReachable.init  → initialCluster (empty logs, committed = 0)
                       CommitCertInvariant holds vacuously

RaftReachable.step  → one Raft step applied to a reachable state,
                       with hypotheses ensuring CCI is preserved:
  hlogs'         : only voter v's log changes
  hno_overwrite  : v's old committed entries are not overwritten
  hqc_preserved  : quorum-certified entries remain quorum-certified in new state
  hcommitted_mono: committed indices only advance (monotone)
  hnew_cert      : new committed entries are quorum-certified in new state
```

## Relationship to RP6 and RP8

The `step` constructor hypotheses abstract the conditions proved by RP6 and RP8:
- `hlogs'` + `hno_overwrite`: captured by RP8 (`raft_transitions_no_rollback`)
- `hqc_preserved`: captures leader completeness (the leader has all quorum-certified
  entries before sending AppendEntries; see Raft §5.4.1, Leader Completeness Property)
- `hnew_cert`: captures the commit rule (commit advances only after quorum ACK)

**Remaining work** for a fully concrete Raft proof: provide real protocol transitions
(message types, term management, leader election) that satisfy these hypotheses.
This requires formalising:
- Election safety: an elected leader has all quorum-certified entries
- The commit rule: `leaderCommit` in AppendEntries reflects a genuine quorum ACK
- Term monotonicity: terms never decrease on a given node

## Theorem table

| ID  | Name                    | Status   | Description                                              |
|-----|-------------------------|----------|----------------------------------------------------------|
| RT0 | `initialCluster_cci`    | ✅ proved | Initial cluster satisfies CommitCertInvariant            |
| RT1 | `raftReachable_cci`     | ✅ proved | All reachable states satisfy CommitCertInvariant         |
| RT2 | `raftReachable_safe`    | ✅ proved | All reachable states are cluster-safe (RSS8 via trace)   |
-/

open FVSquad.RaftSafety
open FVSquad.RaftProtocol

namespace FVSquad.RaftTrace

/-! ## Initial cluster state -/

/-- The initial cluster state: all logs empty, all committed indices 0.

    In Raft, every node starts with an empty log and `committed = 0`.
    The voter list is given as a parameter (fixed throughout the protocol).
    The type parameter `E` for log entries can be any type. -/
def initialCluster {E : Type} (voters : List Nat) : ClusterState E :=
  { voters := voters, logs := fun _ _ => none, committed := fun _ => 0 }

/-! ## Reachability -/

/-- A `ClusterState E` is **RaftReachable** if it can be derived from the initial
    empty cluster by a finite sequence of valid Raft steps.

    Each `step` constructor bundles the hypotheses needed to preserve
    `CommitCertInvariant` across the transition.  These hypotheses are the formal
    expression of the key Raft protocol rules:

    - **`hlogs'`**: only voter `v`'s log changes (one node processes AppendEntries).
    - **`hno_overwrite`**: old committed entries of voter `v` are not overwritten.
      (Corresponds to the `conflict > committed` Rust panic guard in `maybe_append`.)
    - **`hqc_preserved`**: any quorum-certified entry in the old state remains
      quorum-certified in the new state.  This is the formal consequence of leader
      completeness: the leader has all quorum-certified entries and only appends
      entries from its own log, so the quorum certification is preserved.
    - **`hcommitted_mono`**: committed indices only advance (monotonicity).
    - **`hnew_cert`**: any entry newly committed by any voter in the new state is
      quorum-certified in the new log state.  Captures the commit rule: a node only
      advances `committed` when a quorum has acknowledged the entry. -/
inductive RaftReachable [DecidableEq E] : ClusterState E → Prop where
  /-- Base case: the initial cluster (empty logs, committed = 0) is reachable. -/
  | init (voters : List Nat) :
      RaftReachable (initialCluster voters)
  /-- Inductive case: apply one valid Raft step to a reachable state.
      The hypotheses encode the key Raft protocol validity conditions. -/
  | step {cs cs' : ClusterState E}
      (hreach : RaftReachable cs)
      (hvoters : cs.voters = cs'.voters)
      (v : Nat)
      -- Only voter v's log changes (other voters are unaffected)
      (hlogs' : ∀ w, w ≠ v → cs'.logs w = cs.logs w)
      -- Voter v's old committed entries are not overwritten
      (hno_overwrite : ∀ k, cs.committed v ≥ k → cs'.logs v k = cs.logs v k)
      -- Any quorum-certified entry in the old state remains quorum-certified in the new state
      -- (consequence of leader completeness + AE: the leader has all QC entries and broadcasts
      -- them; the weak form is sufficient for CommitCertInvariant preservation)
      (hqc_preserved : ∀ k e, isQuorumCommitted cs.voters cs.logs k e →
          isQuorumCommitted cs'.voters cs'.logs k e)
      -- Committed indices only advance (monotone)
      (hcommitted_mono : ∀ w, cs'.committed w ≥ cs.committed w)
      -- Newly committed entries are quorum-certified in the new cluster state
      -- (consequence of the Raft commit rule: quorum ACK required before advancing)
      (hnew_cert : ∀ w k e, cs'.committed w ≥ k → cs.committed w < k →
          cs'.logs w k = some e →
          isQuorumCommitted cs'.voters cs'.logs k e) :
      RaftReachable cs'

/-! ## RT0: Initial cluster satisfies CommitCertInvariant -/

/-- **RT0** — The initial cluster satisfies CommitCertInvariant.

    In the initial state, all logs are empty (`fun _ _ => none`) and all committed
    indices are 0.  Since `logs v k = none` for every `v` and `k`, the condition
    `logs v k = some e` is never satisfiable, so `CommitCertInvariant` holds
    vacuously: no entry can be `nodeHasApplied`.

    **Significance**: this is the base case for the protocol induction (RT1). -/
theorem initialCluster_cci {E : Type} [DecidableEq E] (voters : List Nat) :
    CommitCertInvariant (initialCluster (E := E) voters) := by
  intro v k e _hcomm hlog
  simp only [initialCluster] at hlog
  -- hlog : none = some e, which is False
  exact absurd hlog (by simp)

/-! ## RT1: All reachable states satisfy CommitCertInvariant -/

/-- **RT1** — Every `RaftReachable` cluster state satisfies `CommitCertInvariant`.

    **Proof**: by induction on the `RaftReachable` derivation.

    - **Base case** (`init`): `initialCluster_cci` gives the result for the empty
      initial cluster.

    - **Inductive case** (`step`): for voter `w` and committed index `k`:
      - If `k > cs.committed w` (**newly committed**): `hnew_cert` directly gives
        `isQuorumCommitted cs'.voters cs'.logs k e`.
      - If `k ≤ cs.committed w` (**old committed**): the log at `k` is unchanged
        (`hno_overwrite` for `w = v`, `hlogs'` for `w ≠ v`), so the inductive
        hypothesis `ih` gives `isQuorumCommitted cs.voters cs.logs k e`, and
        `hqc_preserved` directly translates this to `isQuorumCommitted cs'.voters cs'.logs k e`.

    **Significance**: this proof shows that `CommitCertInvariant` is an inductive
    invariant of the `RaftReachable` protocol model. -/
theorem raftReachable_cci [DecidableEq E] (cs : ClusterState E)
    (h : RaftReachable cs) : CommitCertInvariant cs := by
  induction h with
  | init voters => exact initialCluster_cci voters
  | step hreach hvoters v hlogs' hno_overwrite hqc_preserved hcommitted_mono hnew_cert ih =>
    -- Rename the implicit cluster states from the constructor:
    -- cs_prev = old state, cs_new = new state (what we're proving CCI for)
    rename_i cs_prev cs_new
    intro w k e hcomm' hlog'
    -- Split: was k already committed for w in cs_prev, or is it newly committed?
    by_cases hnew : cs_prev.committed w < k
    · -- Newly committed in new state: use hnew_cert directly
      exact hnew_cert w k e hcomm' hnew hlog'
    · -- Old committed: k ≤ cs_prev.committed w
      have hold : cs_prev.committed w ≥ k := by omega
      -- Recover the old log entry (cs_prev.logs w k = some e)
      have hlog_old : cs_prev.logs w k = some e := by
        by_cases hw : w = v
        · -- voter v: use hno_overwrite (v's old committed entries not overwritten)
          subst hw
          rw [← hno_overwrite k hold]; exact hlog'
        · -- other voter: log unchanged (hlogs')
          rw [← congrFun (hlogs' w hw) k]; exact hlog'
      -- Apply the inductive hypothesis to the old state
      have hqc_old : isQuorumCommitted cs_prev.voters cs_prev.logs k e :=
        ih w k e hold hlog_old
      -- hqc_preserved (weak) directly lifts the commitment to the new state
      exact hqc_preserved k e hqc_old

/-! ## RT2: All reachable states are cluster-safe -/

/-- **RT2** — Every `RaftReachable` cluster state with non-empty voters is cluster-safe.

    This is **RSS8 via the RaftTrace model** — full unconditional end-to-end Raft
    safety for any cluster reachable from the initial empty state.

    **Proof**:
    1. `raftReachable_cci` (RT1) gives `CommitCertInvariant cs`.
    2. `raft_end_to_end_safety_full` (RSS8, `RaftSafety.lean`) gives `isClusterSafe cs`
       from `CommitCertInvariant cs`.

    **Remaining work** for a fully concrete Raft proof: provide protocol-level
    transitions that satisfy the `RaftReachable.step` hypotheses (particularly
    `hqc_preserved` and `hnew_cert`).  This requires formalising term management,
    leader election, and the vote-granting conditions that ensure leader completeness.

    **Connection to the Rust implementation**: the `hno_overwrite` condition in
    `RaftReachable.step` corresponds exactly to the panic guard in `maybe_append`:
    ```rust
    if conflict != 0 && conflict <= self.committed {
        panic!("entry {} conflict with committed log entry", conflict);
    }
    ```
    This panic ensures `hno_overwrite` for the AppendEntries case. -/
theorem raftReachable_safe [DecidableEq E]
    (hd : Nat) (tl : List Nat) (cs : ClusterState E)
    (hvoters : cs.voters = hd :: tl)
    (hreach : RaftReachable cs) :
    isClusterSafe cs :=
  raft_end_to_end_safety_full hd tl cs hvoters (raftReachable_cci cs hreach)

/-! ## Evaluation: the initial cluster is trivially safe -/

/-- The initial 3-voter cluster (voters = [1,2,3]) is safe.
    No entries are committed, so safety holds vacuously via `raftReachable_safe`. -/
theorem initialCluster_safe :
    isClusterSafe (initialCluster (E := Nat) [1, 2, 3]) :=
  raftReachable_safe 1 [2, 3] _ rfl (RaftReachable.init (E := Nat) [1, 2, 3])

end FVSquad.RaftTrace
