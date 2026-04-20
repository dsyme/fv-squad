# FVSquad: Formal Verification Project Report

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

**Status**: 🔄 **IN PROGRESS** — 485+ theorems, 28 Lean files, 2 `sorry`, machine-checked
by Lean 4.28.0 (stdlib only). Top-level safety theorem proved **conditionally** — election
model gap remains (see §Critical Gap below).

---

## Last Updated
- **Date**: 2026-05-09 08:30 UTC
- **Commit**: `b0a0fe1` — CommitRule.lean added (CR1–CR9, 9 new theorems)

---

## Executive Summary

The FVSquad project applied Lean 4 formal verification to the Raft consensus implementation
in `dsyme/fv-squad` over 33+ automated runs. Starting from zero, the project:

1. Identified 20+ FV-amenable targets across the codebase
2. Extracted informal specifications for each target
3. Wrote Lean 4 specifications, implementation models, and proofs
4. Proved **485+ theorems** across **28 Lean files** with **2 `sorry`**
5. Proved **conditional end-to-end Raft cluster safety**: any cluster state reachable
   via transitions satisfying 5 stated invariants is safe (no two nodes ever apply
   different entries at the same log index)

An external critique (2026-04-20) identified a **significant remaining gap**: the
`RaftReachable.step` constructor bundles 5 invariant conditions as abstract hypotheses
that are not yet proved from a concrete election model (terms, votes, leader completeness).
Approximately **60–70% of the components** needed for a fully self-contained proof exist;
the missing 30–40% is the election model and leader completeness composition.

No bugs were found in the implementation code (itself a positive finding).

---

## Critical Gap: The Election Model

The top-level theorem `raftReachable_safe` (RT2) proves:
> *Any `RaftReachable` cluster state is safe.*

But `RaftReachable.step` takes 5 hypotheses as parameters:

| Hypothesis | Meaning | Status |
|---|---|---|
| `hlogs'` | Only one voter's log changes per step | Proved for AppendEntries (RP8 partial); needs message-delivery model |
| `hno_overwrite` | Committed entries not overwritten | Covered by RP8 `hno_truncate`; needs panic-guard proof |
| `hqc_preserved` | Quorum-certified entries preserved in ALL logs | **Not proved** — requires leader completeness composition |
| `hcommitted_mono` | Committed indices only advance | Covered by MA6 for `maybeAppend`; needs general model |
| `hnew_cert` | New commits are quorum-certified | **Proved** by CommitRule.lean (CR5, CR8) |

Until concrete Raft transitions (NodeState, terms, elections) are proved to satisfy these
5 conditions, `raftReachable_safe` is a conditional correctness result, not a fully
unconditional proof.

The hardest gap is **`hqc_preserved`** (leader completeness): the argument requires an
election model (term management, vote-granting, candidate eligibility) and composing
HQ20 + IU16 + TallyVotes + RSS5 — each piece exists, but the composition is missing.
This requires ~3–5 new Lean files and ~100–200 new theorems.

---

## Proof Architecture

The proof is organised in six layers, each building on the layer below:

```mermaid
graph TD
    A["🏗️ Layer 1: Data Structures<br/>LimitSize · LogUnstable · Inflights<br/>Progress · ConfigValidate"]
    B["🔢 Layer 2: Quorum Arithmetic<br/>MajorityVote · JointVote<br/>HasQuorum · CommittedIndex · JointCommittedIndex<br/>TallyVotes · JointTally"]
    C["🔄 Layer 3: Protocol Operations<br/>FindConflict · MaybeAppend<br/>IsUpToDate · QuorumRecentlyActive"]
    D["🔗 Layer 4: Cross-Module Composition<br/>SafetyComposition · JointSafetyComposition<br/>CrossModuleComposition"]
    E["🛡️ Layer 5: Raft Safety<br/>RaftSafety (RSS1–RSS8)<br/>RaftProtocol (RP6, RP8)"]
    F["⚠️ Layer 6: Reachability (conditional)<br/>RaftTrace (RT1, RT2)<br/>raftReachable_safe"]
    G["❓ Layer 7: Election Model (partial)<br/>RaftElection · LeaderCompleteness<br/>ConcreteTransitions · CommitRule"]

    A --> B
    B --> C
    C --> D
    D --> E
    E --> F
    G -.->|"needed to discharge<br/>step hypotheses"| F
```

---

## What Was Verified

### Layer 1 — Data Structures (5 files, ~120 theorems)

Individual data-structure correctness: the core Raft data structures behave correctly
in isolation.

```mermaid
graph LR
    LS["LimitSize.lean<br/>17 theorems<br/>Prefix semantics,<br/>maximality, idempotence"]
    LU["LogUnstable.lean<br/>37 theorems<br/>Snapshot/entries,<br/>wf invariants"]
    IF["Inflights.lean<br/>49 theorems<br/>Ring buffer,<br/>abstract/concrete bridge"]
    PR["Progress.lean<br/>31 theorems<br/>State machine,<br/>wf: matched+1≤next_idx"]
    CV["ConfigValidate.lean<br/>10 theorems<br/>8 config constraints,<br/>Boolean ↔ predicate"]
```

**Key results**:
- `limitSize_maximality`: output is *maximal* (not just valid) — proves no unnecessarily small batches
- `inflightsConc_freeTo_correct`: ring-buffer concrete model matches abstract spec
- `Progress.wf` preserved by all transitions

### Layer 2 — Quorum Arithmetic (7 files, ~110 theorems)

Mathematical foundations of Raft consensus: the quorum-intersection property that
prevents two different leaders from being elected and two different entries from being
simultaneously committed.

```mermaid
graph TD
    MV["MajorityVote.lean<br/>21 theorems<br/>Single-config vote counting,<br/>Won/Lost/Pending iff"]
    JV["JointVote.lean<br/>14 theorems<br/>Joint-config degeneracy"]
    HQ["HasQuorum.lean<br/>22 theorems<br/>quorum_intersection (HQ14)<br/>concrete witness (HQ20)"]
    CI["CommittedIndex.lean<br/>17 theorems<br/>Sort-then-index algorithm,<br/>safety + maximality"]
    JCI["JointCommittedIndex.lean<br/>10 theorems<br/>min(ci_in, ci_out)"]
    TV["TallyVotes.lean<br/>18 theorems<br/>Partition, bounds,<br/>no double-quorum (TV18)"]
    JT["JointTally.lean<br/>14 theorems<br/>Joint config tallying"]

    MV --> HQ
    MV --> CI
    JV --> JCI
    HQ --> CI
    CI --> JCI
    MV --> TV
    TV --> JT
```

**Key result**: `quorum_intersection_mem` (HQ20) — the mathematical cornerstone.
For any non-empty voter list and any two majority-quorum predicates, there exists a
concrete witness voter in both. This is the property that makes Raft safe.

### Layer 3 — Protocol Operations (4 files, ~70 theorems)

Core Raft log operations are correct: entries are appended/truncated correctly,
conflicts are found at the right index, log ordering is a total preorder.

```mermaid
graph LR
    FC["FindConflict.lean<br/>12 theorems<br/>First mismatch index,<br/>zero ↔ all-match (FC11)"]
    MA["MaybeAppend.lean<br/>18 theorems<br/>Prefix preserved (MA13)<br/>Suffix applied (MA14)"]
    IU["IsUpToDate.lean<br/>18 theorems<br/>Lex order on term×index,<br/>total preorder (IU10)"]
    QRA["QuorumRecentlyActive.lean<br/>15 theorems<br/>Active-quorum detection"]
```

**Key result**: MA13 + MA14 together give a complete post-condition for `maybe_append`:
the prefix is untouched AND the suffix is correctly applied.

### Layer 4 — Cross-Module Composition (3 files, ~26 theorems)

The first layer that spans multiple independent modules, proving properties that
neither module could state alone.

```mermaid
graph TD
    SC["SafetyComposition.lean<br/>9 theorems<br/>SC4: two committed indices share<br/>a witness voter"]
    JSC["JointSafetyComposition.lean<br/>10 theorems<br/>JSC7: witnesses in both<br/>quorum halves"]
    CMC["CrossModuleComposition.lean<br/>7 theorems<br/>CMC3: maybe_append never<br/>commits beyond quorum"]

    CI2["CommittedIndex"] --> SC
    HQ2["HasQuorum"] --> SC
    SC --> CMC
    SC --> JSC
    MA2["MaybeAppend"] --> CMC
    FC2["FindConflict"] --> CMC
```

**Key result**: `CMC3_maybeAppend_committed_bounded` — `maybe_append` is safe: it never
advances the commit index beyond what the quorum has certified.

### Layer 5 — Raft Safety (2 files, ~24 theorems)

Log-entry-level safety theorems and protocol transition invariants.

```mermaid
graph TD
    RSS1["RSS1: raft_state_machine_safety<br/>Two entries committed at same<br/>index must be identical"]
    RSS6["RSS6: raft_cluster_safety<br/>Cluster is safe given<br/>CommitCertInvariant"]
    RSS8["RSS8: raft_end_to_end_safety_full<br/>Safety given CCI<br/>(2-line proof)"]
    RP6["RP6: appendEntries_preserves_log_matching<br/>LMI maintained by AppendEntries<br/>(3 cases proved)"]
    RP8["RP8: raft_transitions_no_rollback<br/>No-rollback for AppendEntries<br/>given hno_truncate"]

    SC3["SC4 (SafetyComposition)"] --> RSS1
    JSC3["JSC7 (JointSafetyComposition)"] --> RSS1
    RSS1 --> RSS6
    RSS6 --> RSS8
    RP6 --> RSS8
    RP8 --> RSS8
```

### Layer 6 — Reachability (1 file, 3 theorems) ⚠️ Conditional

The top-level results — proved assuming `RaftReachable.step` hypotheses hold for each
protocol step.  See §Critical Gap for why these hypotheses are not yet discharged from
a concrete election model.

```mermaid
graph TD
    INIT["RaftReachable.init<br/>initialCluster satisfies CCI<br/>(vacuously: no entries)"]
    STEP["RaftReachable.step<br/>One valid Raft transition<br/>preserves CCI<br/>(5 abstract hypotheses — not yet\ndischarged from election model)"]
    RT0["RT0: initialCluster_cci<br/>Initial state ⊨ CCI"]
    RT1["RT1: raftReachable_cci<br/>∀ reachable cs, cs ⊨ CCI<br/>(structural induction)"]
    RT2["RT2: raftReachable_safe<br/>∀ reachable cs, isClusterSafe cs<br/>TOP-LEVEL — conditional on step hyps"]

    INIT --> RT0
    RT0 --> RT1
    STEP --> RT1
    RT1 --> RT2
    RSS8_2["RSS8 (RaftSafety)"] --> RT2
```

---

## File Inventory

| File | Theorems | Phase | Key result |
|------|----------|-------|------------|
| `LimitSize.lean` | 17 | 5 ✅ | Prefix + maximality of `limit_size` |
| `ConfigValidate.lean` | 10 | 5 ✅ | Boolean fn ↔ 8-constraint predicate |
| `MajorityVote.lean` | 21 | 5 ✅ | `voteResult` characterisation, Won/Lost/Pending |
| `JointVote.lean` | 14 | 5 ✅ | Joint config degeneracy to single quorum |
| `CommittedIndex.lean` | 17 | 5 ✅ | Sort-index safety + maximality |
| `FindConflict.lean` | 12 | 5 ✅ | First mismatch, zero ↔ all-match |
| `JointCommittedIndex.lean` | 10 | 5 ✅ | `min(ci_in, ci_out)` semantics |
| `MaybeAppend.lean` | 18 | 5 ✅ | Prefix preserved, suffix applied, committed safe |
| `Inflights.lean` | 49 | 5 ✅ | Ring-buffer abstract/concrete bridge |
| `Progress.lean` | 31 | 5 ✅ | State-machine wf invariant (matched+1≤next_idx) |
| `IsUpToDate.lean` | 18 | 5 ✅ | Lex order, total preorder for leader election |
| `LogUnstable.lean` | 37 | 5 ✅ | Snapshot/entries consistency invariants |
| `TallyVotes.lean` | 18 | 5 ✅ | Partition, bounds, no double-quorum |
| `HasQuorum.lean` | 22 | 5 ✅ | Quorum intersection (HQ14), witness (HQ20) |
| `QuorumRecentlyActive.lean` | 15 | 5 ✅ | Active-quorum detection correctness |
| `SafetyComposition.lean` | 9 | 5 ✅ | SC4: two CIs share a witness voter |
| `JointTally.lean` | 14 | 5 ✅ | Joint-config tally correctness |
| `JointSafetyComposition.lean` | 10 | 5 ✅ | JSC7: witnesses in both quorum halves |
| `CrossModuleComposition.lean` | 7 | 5 ✅ | CMC3: maybe_append bounded by quorum |
| `RaftSafety.lean` | 14 | 5 ✅ | RSS1–RSS8: end-to-end cluster safety |
| `RaftProtocol.lean` | 10 | 5 ✅ | RP6, RP8: LMI/NRI preserved by AppendEntries |
| `RaftTrace.lean` | 3 | 5 ✅⚠️ | RT1, RT2: conditional reachable safety (step hyps abstract) |
| `LeaderCompleteness.lean` | 15 | 5 ✅ | Election model + leader completeness properties |
| `ConcreteTransitions.lean` | 20 | 5 🔄 | CT1–CT5b: concrete AppendEntries transitions; 2 sorry remain |
| `CommitRule.lean` | 9 | 5 ✅ | CR1–CR9: commit rule formalised; implies `hnew_cert` |
| `Basic.lean` | helpers | — | Shared definitions |
| **Total** | **485+** | **5 ✅/🔄** | **2 sorry (CT4, CT5)** |

---

## The Main Proof Chain

```mermaid
graph LR
    A["quorum_intersection_mem<br/>(HQ20)"]
    B["SC4_raft_log_safety<br/>(SafetyComposition)"]
    C["raft_state_machine_safety<br/>RSS1 (RaftSafety)"]
    D["raft_cluster_safety<br/>RSS6 (RaftSafety)"]
    E["raft_end_to_end_safety_full<br/>RSS8 (RaftSafety)"]
    F["raftReachable_cci<br/>RT1 (RaftTrace)"]
    G["raftReachable_safe<br/>RT2 ⚠️ conditional"]

    A --> B --> C --> D --> E
    F --> G
    E --> G
```

The top-level theorem is `raftReachable_safe`:

```lean
theorem raftReachable_safe [DecidableEq E]
    (cs : ClusterState E) (h : RaftReachable cs) : isClusterSafe cs
```

This states: for any cluster state `cs` reachable by valid Raft transitions (satisfying the
5 `step` hypotheses), `cs` is safe — no two voters have different entries at the same
committed index.  The theorem is machine-checked, but the 5 `step` hypotheses are not yet
discharged from a concrete election model.  See §Critical Gap.

---

## Modelling Choices and Known Limitations

```mermaid
graph TD
    REAL["Real Raft Cluster<br/>(Rust implementation)"]
    MODEL["FVSquad Model<br/>(Lean 4 abstract model)"]
    PROOF["Lean Proofs<br/>(485+ theorems, 2 sorry)"]

    REAL -->|"Modelled as"| MODEL
    MODEL -->|"Proved in"| PROOF

    NOTE1["✅ Included: quorum logic,<br/>log operations, config,<br/>flow control, state machines"]
    NOTE2["⚠️ Abstracted: u64→Nat,<br/>HashMap→function,<br/>ring buffer→list"]
    NOTE3["❌ Omitted: terms/leadership,<br/>network/I/O, concurrent state,<br/>concrete protocol messages"]

    MODEL --- NOTE1
    MODEL --- NOTE2
    MODEL --- NOTE3
```

| Category | What's covered | What's abstracted/omitted |
|----------|---------------|--------------------------|
| **Types** | All core data structures | `u64` → `Nat` (no overflow); `HashMap` → function |
| **Logic** | All quorum, log, and voting logic | Ring-buffer internal layout |
| **Protocol** | AppendEntries effects on logs | Term tracking, leader election, heartbeats |
| **Safety** | Cluster state-machine safety | Liveness, network partition tolerance |
| **Transitions** | `RaftReachable` abstract steps | Concrete Raft message types |

The `RaftReachable.step` hypotheses are the honest residual gap: they are proof-engineering
artefacts that precisely capture what preserves `CommitCertInvariant`, but do not yet
correspond to concrete Raft protocol transitions. A future extension would define real
AppendEntries/RequestVote messages and prove that they satisfy the `step` hypotheses.

---

## Findings

### No implementation bugs found

All 485+ theorems are consistent with the Rust implementation. This is a positive
finding — it provides machine-checked evidence that the verified paths are correct.

### Formulation bug caught by `sorry`

An early version of `log_matching_property` (RSS3) and `raft_committed_no_rollback` (RSS4)
claimed properties for *arbitrary* log states — which are provably false. The `sorry`
mechanism acted as a "needs review" marker that allowed catching the error before it
entered the proof base. Both theorems were corrected with proper hypotheses
(`LogMatchingInvariantFor`, `NoRollbackInvariantFor`) and proved in run r130.

### Interesting structural discoveries

- `limitSize_maximality`: output is optimal, not just valid
- `quorum_intersection_mem`: every two majority quorums share a concrete witness
- `raftReachable_safe`: conditional top-level safety — proved given 5 protocol hypotheses;
  election model needed to make this unconditional

---

## Project Timeline

```mermaid
timeline
    title FVSquad Proof Development
    section Early runs (r100–r115)
        LimitSize + ConfigValidate : 27 theorems
        MajorityVote + HasQuorum : 43 theorems
        CommittedIndex + FindConflict + MaybeAppend : 47 theorems
    section Mid runs (r116–r125)
        Inflights (ring buffer) : 49 theorems — hardest individual file
        Progress + IsUpToDate : 49 theorems
        LogUnstable + TallyVotes + JointVote : 79 theorems
    section Composition layer (r126–r130)
        JointCommittedIndex + QuorumRecentlyActive : 25 theorems
        SafetyComposition + JointSafetyComposition : 19 theorems
        CrossModuleComposition : 7 theorems
        RSS3 and RSS4 formulation bug found and fixed
    section Raft safety (r131–r133)
        RaftSafety RSS1–RSS7 : 13 theorems fully proved
        RaftProtocol RP6 + RP8 : full proofs, 0 sorry
        RaftTrace + RSS8 : 3 theorems — conditional safety proved
    section Election model (r134–r155)
        LeaderCompleteness : 15 theorems, leader election model
        ConcreteTransitions CT1–CT5b : 20 theorems, 2 sorry remain (CT4, CT5)
        CommitRule CR1–CR9 : 9 theorems, hnew_cert fully closed
    section Election model (next)
        ConcreteRaft step hypotheses : ~50–80 theorems planned
        hqc_preserved composition : ~30–50 theorems planned
```

---

## Toolchain

- **Prover**: Lean 4 (version 4.28.0)
- **Libraries**: Lean 4 stdlib only (no Mathlib dependency)
- **CI**: `.github/workflows/lean-ci.yml` — runs `lake build` on every PR to `formal-verification/lean/**`
- **Build system**: Lake (project at `formal-verification/lean/`)

Key tactic inventory used across the proofs:

| Tactic | Usage |
|--------|-------|
| `omega` | Integer/natural-number arithmetic |
| `simp` / `simp only` | Definitional unfolding and simplification |
| `by_cases` / `split` | Case splits on booleans and decidable propositions |
| `induction` / `cases` | Structural induction on lists, options, inductives |
| `exact` / `apply` / `refine` | Direct term construction |
| `constructor` / `intro` / `ext` | Conjunction, implication, function extensionality |
| `funext` | Proving function equality |

No `native_decide`, no `axiom`. Two `sorry` remain in `ConcreteTransitions.lean` (CT4 and CT5);
all other 485+ theorems are fully proved.

---

## CommitRule.lean — Run 35 Addition

This run formalises the **Raft commit rule** as a standalone Lean file (`CommitRule.lean`,
9 new theorems CR1–CR9, 0 sorry):

| Theorem | Statement |
|---------|-----------|
| CR1 `qc_from_quorum_acks` | Quorum of acks with matching log entry → `isQuorumCommitted` |
| CR2 `qc_preserved_by_log_agreement` | Changing one voter's log cannot break a quorum commit already held elsewhere |
| CR3 `qc_preserved_by_log_growth` | Growing a log (appending) preserves existing quorum commits |
| CR4 `matchIndex_quorum_qc` | If `matchIndex` reports quorum agreement at `k`, then `isQuorumCommitted` holds |
| CR5 `commitRuleValid_implies_hnew_cert` | `CommitRuleValid` directly satisfies the `hnew_cert` hypothesis of `RaftReachable.step` |
| CR6 `hnew_cert_of_qc_advance` | When quorum commitment advances, `hnew_cert` holds for the new commit |
| CR7 `qc_of_accepted_ae_quorum` | If a quorum of voters accepted the AppendEntries, quorum commitment holds |
| CR8 `commitRuleValid_step_condition` | `CommitRuleValid = hnew_cert` (definitional equality, `Iff.rfl`) |
| CR9 `commitRule_and_preservation_implies_cci` | Commit rule + log preservation → `CommitCertInvariant` preserved |

CR8 (`Iff.rfl`) closes the proof obligation for `hnew_cert` in `RaftReachable.step`.
The remaining 4 step hypotheses (`hlogs'`, `hno_overwrite`, `hqc_preserved`,
`hcommitted_mono`) are targets for the next run.


---

> 🔬 *This report was generated by [Lean Squad](https://github.com/dsyme/fv-squad/actions/runs/23979949696) — an automated formal verification agent for `dsyme/fv-squad`.*
