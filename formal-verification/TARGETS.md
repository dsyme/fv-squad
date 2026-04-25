# FV Targets

> 🔬 *Lean Squad — automated formal verification for this repository.*

Prioritised target list. Phases: 1=Research, 2=Informal Spec, 3=Lean Spec, 4=Lean Impl, 5=Proofs.

## Completed Targets (Phase 5)

| Priority | ID | File | Function | Phase | Notes |
|----------|----|------|----------|-------|-------|
| 1 | `limit_size` | `src/util.rs` | `limit_size` | 5 ✅ | All 17 theorems proved (0 sorry). `FVSquad/LimitSize.lean`. |
| 2 | `config_validate` | `src/config.rs` | `Config::validate` | 5 ✅ | All 10 theorems proved (0 sorry). `FVSquad/ConfigValidate.lean`. |
| 3 | `vote_result` | `src/quorum/majority.rs` | `Configuration::vote_result` | 5 ✅ | 21 theorems proved (0 sorry). `FVSquad/MajorityVote.lean`. |
| 4 | `committed_index` | `src/quorum/majority.rs` | `Configuration::committed_index` | 5 ✅ | ALL 17 theorems proved (0 sorry). Safety, maximality, monotonicity all proved. `FVSquad/CommittedIndex.lean`. |
| 5 | `find_conflict` | `src/raft_log.rs` | `RaftLog::find_conflict` | 5 ✅ | ALL 12 theorems proved (0 sorry). `FVSquad/FindConflict.lean`. |
| 5b | `find_conflict_by_term` | `src/raft_log.rs` | `RaftLog::find_conflict_by_term` | 5 ✅ | 10 theorems proved (0 sorry): range bound, term bound, maximality, identity, out-of-range, always-Some, delegation, base-case, monotone helper. `FVSquad/FindConflictByTerm.lean`. |
| 6 | `maybe_append` | `src/raft_log.rs` | `RaftLog::maybe_append` | 5 ✅ | 18 theorems proved (0 sorry). `FVSquad/MaybeAppend.lean`. |
| 7 | `joint_vote_result` | `src/quorum/joint.rs` | `JointConfig::vote_result` | 5 ✅ | 14 theorems proved (0 sorry). `FVSquad/JointVote.lean`. |
| 8 | `joint_committed_index` | `src/quorum/joint.rs` | `JointConfig::committed_index` | 5 ✅ | 10 theorems proved (0 sorry). `FVSquad/JointCommittedIndex.lean`. |
| 9 | `inflights` | `src/tracker/inflights.rs` | ring buffer ops | 5 ✅ | 49 theorems proved (0 sorry). `FVSquad/Inflights.lean`. |
| 10 | `progress` | `src/tracker/progress.rs` | state machine | 5 ✅ | 31 theorems proved (0 sorry). `FVSquad/Progress.lean`. |
| 12 | `is_up_to_date` | `src/raft_log.rs` | log freshness comparison | 5 ✅ | 18 theorems proved (0 sorry). `FVSquad/IsUpToDate.lean`. |
| 13 | `log_unstable` | `src/log_unstable.rs` | unstable log segment ops | 5 ✅ | 37 theorems proved (0 sorry). `FVSquad/LogUnstable.lean`. |
| 14 | `tally_votes` | `src/tracker.rs` | `ProgressTracker::tally_votes` | 5 ✅ | 18 theorems proved (0 sorry). `FVSquad/TallyVotes.lean`. |
| 15 | `has_quorum` | `src/tracker.rs` | `ProgressTracker::has_quorum` | 5 ✅ | 22 theorems proved (0 sorry). `FVSquad/HasQuorum.lean`. |
| 16 | `quorum_recently_active` | `src/tracker.rs` | `ProgressTracker::quorum_recently_active` | 5 ✅ | 15 theorems proved (0 sorry). `FVSquad/QuorumRecentlyActive.lean`. |
| 17 | `safety_composition` | cross-module | `committedIndex` × `hasQuorum` × `quorumRecentlyActive` | 5 ✅ | 9 theorems proved (0 sorry). `FVSquad/SafetyComposition.lean`. |
| 18 | `joint_tally` | `src/tracker.rs` | `ProgressTracker::tally_votes` (joint) | 5 ✅ | 14 theorems proved (0 sorry). `FVSquad/JointTally.lean`. |
| 19 | `joint_safety_composition` | cross-module | `jointCommittedIndex` × `hasQuorum` × `SafetyComposition` | 5 ✅ | 10 theorems proved (0 sorry). `FVSquad/JointSafetyComposition.lean`. |
| 20 | `raft_protocol` | `src/raft_log.rs` + `proto/` | AppendEntries / RequestVote transitions | 5 ✅ | 10 theorems proved (0 sorry). RP6 and RP8 proved. `FVSquad/RaftProtocol.lean`. |
| 23 | `raft_trace` | `RaftSafety.lean` + `RaftProtocol.lean` | Protocol-level reachability model | 5 ✅⚠️ | RT0+RT1+RT2 proved (0 sorry), but `step` hypotheses are abstract axioms — not yet discharged from a concrete election model. `FVSquad/RaftTrace.lean`. |
| 24 | `progress_tracker` | `src/tracker.rs` | `ProgressTracker` membership ops | 5 ✅ | PT1-PT21 proved (Run 96+102): all_wf preservation, peer membership, `hasPeer`/`removePeer`/`insertPeer`. `FVSquad/ProgressTracker.lean`. |
| 25 | `configuration_invariants` | `src/tracker.rs` | `Configuration` `VotersLearnersDisjoint` invariant | 5 ✅ | CI1-CI8 proved (Run 102): structural invariant, disjointness under ops. Correspondence: `ConfigurationInvariantsCorrespondence.lean` (15 `#guard`, Run 103). `FVSquad/ConfigurationInvariants.lean`. |
| 26 | `multistep_reachability` | cross-module | N-step `RaftReachable` + cluster safety | 5 ✅ | MS1-MS7 proved (Run 101): `ValidAEList`, N-step safety certificate, `committed_mono` across sequences. `FVSquad/MultiStepReachability.lean`. |

## Active / Future Targets — Closing the Election Model Gap

An external critique (2026-04-20) identified that `RaftReachable.step` bundles 5 hypotheses
as abstract axioms.  The following targets are **required to make the proof fully self-contained**.
See `CRITIQUE.md §Critical Gap Analysis` for the full analysis.

| Priority | ID | Proposed file | Goal | Phase | Difficulty | Gap addressed |
|----------|----|--------------|------|-------|-----------|---------------|
| **A1** | `election_model` | `FVSquad/RaftElection.lean` | Model `NodeState` (currentTerm, votedFor, role), vote-granting rules, term monotonicity | 5 ✅ | Medium | Completed: RT1-RT15, RI1-RI15, `processVoteRequest`, `electionSafety`. All proved (0 sorry). |
| **A2** | `election_safety` | `FVSquad/RaftElection.lean` | Prove at most one leader per term (ElectionSafety); uses HQ20 + TallyVotes | 5 ✅ | Medium-high | `electionSafety` proved. RI11-RI15 cluster-level invariants. |
| **A3** | `leader_completeness` | `FVSquad/LeaderCompleteness.lean` | Compose HQ20 + IU16 + RSS5: elected leader has all quorum-certified entries | 1 | **High** | `hqc_preserved` (full discharge) |
| **A4** | `concrete_transitions` | `FVSquad/ConcreteRaft.lean` | AppendEntries + RequestVote with terms; discharge `hlogs'`, `hno_overwrite`, `hcommitted_mono` | 1 | Medium | 3 of 5 step hypotheses |
| **A5** | `commit_rule` | `FVSquad/ConcreteRaft.lean` | Discharge `hnew_cert` — commit only after quorum ACK; builds on CMC3 | 1 | Medium-high | `hnew_cert` |

## Other Pending Targets

| Priority | ID | File | Function | Phase | Notes |
|----------|----|------|----------|-------|-------|
| 11 | `progress_set` | `src/tracker/progress_set.rs` | quorum tracking over progress map | 1 | Formalise `ProgressSet::quorum_active` and quorum detection across the voter progress map. |
| 21 | `read_only` | `src/read_only.rs` | `ReadOnly` struct + 5 methods | 5 ✅ | ReadIndex linearisability bookkeeping (Raft §6.4). `FVSquad/ReadOnly.lean` (15T: RO1–RO14, all proved, 0 sorry). |
| 22 | `raft_log_append` | `src/raft_log.rs` | `RaftLog::append` | 5 ✅ | Lean spec + impl (Run 45+46) + P6/P7 proved (Run 50). `FVSquad/RaftLogAppend.lean` (14+ theorems). Correspondence test: `FVSquad/RaftLogAppendCorrespondence.lean` (Run 82, 21 `#guard`, all 3 truncate_and_append branches covered). |
| 27 | `has_next_entries` | `src/raft_log.rs` | `applied_index_upper_bound` / `has_next_entries_since` | 5 ✅ | **New — Run 111.** Informal spec: `specs/has_next_entries_informal.md`. Lean spec: `FVSquad/HasNextEntries.lean` (14T: HNE1–HNE14, all proved, 0 sorry). Models the interaction between `committed`, `persisted`, and `max_apply_unpersisted_log_limit`. |

## Correspondence Test Coverage (Run 111) — 23 targets, ~455 `#guard`

All major proof targets now have correspondence-validated Lean models. Every target below
has a `*Correspondence.lean` file with `#guard` tests and a matching Rust `test_*_correspondence`.

| Target | Lean Correspondence File | `#guard` | Rust Test | Level |
|--------|--------------------------|---------|-----------|-------|
| `find_conflict` | `FindConflictCorrespondence.lean` | 27 | ✅ | abstraction |
| `maybe_append` | `MaybeAppendCorrespondence.lean` | 35 | ✅ | exact |
| `is_up_to_date` | `IsUpToDateCorrespondence.lean` | 14 | ✅ | exact |
| `committed_index` | `CommittedIndexCorrespondence.lean` | 13 | ✅ | abstraction |
| `limit_size` | `LimitSizeCorrespondence.lean` | 12 | ✅ | abstraction |
| `config_validate` | `ConfigValidateCorrespondence.lean` | 14 | ✅ | exact |
| `inflights` | `InflightsCorrespondence.lean` | 14 | ✅ | abstraction |
| `log_unstable` | `LogUnstableCorrespondence.lean` | 14 | ✅ | exact |
| `tally_votes` | `TallyVotesCorrespondence.lean` | 12 | ✅ | exact |
| `vote_result` | `VoteResultCorrespondence.lean` | 17 | ✅ | exact |
| `has_quorum` | `HasQuorumCorrespondence.lean` | 17 | ✅ | exact |
| `read_only` | `ReadOnlyCorrespondence.lean` | 16 | ✅ | exact |
| `find_conflict_by_term` | `FindConflictByTermCorrespondence.lean` | 19 | ✅ | exact |
| `progress` | `ProgressCorrespondence.lean` | 55 | ✅ | abstraction |
| `maybe_persist` | `MaybePersistCorrespondence.lean` | 21 | ✅ | abstraction |
| `maybe_commit` | `MaybeCommitCorrespondence.lean` | 19 | ✅ | exact |
| `raft_log_append` | `RaftLogAppendCorrespondence.lean` | 21 | ✅ | abstraction |
| `maybe_persist_fui` | `MaybePersistFUICorrespondence.lean` | 20 | ✅ | abstraction |
| `quorum_recently_active` | `QuorumRecentlyActiveCorrespondence.lean` | 14 | ✅ | abstraction |
| `joint_vote_result` | `JointVoteCorrespondence.lean` | 15 | ✅ | exact |
| `election_vote_granted` | `ElectionCorrespondence.lean` | 23 | ✅ | exact |
| `configuration_invariants` | `ConfigurationInvariantsCorrespondence.lean` | 15 | ✅ (Run 103) | exact |
| `uncommitted_state` | `UncommittedStateCorrespondence.lean` | 13 | ✅ (Run 110) | abstraction |
| `next_entries` | `NextEntriesCorrespondence.lean` | 28 | ✅ (Run 113) | abstraction |
| `has_next_entries` | `HasNextEntriesCorrespondence.lean` | 33 | ✅ (Run 114) | exact |
| **Total** | **25 files** | **~513** | **25 Rust tests** | — |

### Note (Run 110): `uncommitted_state` correspondence finding

`UncommittedStateCorrespondence.lean` (Run 110) documents a **noLimit fast-path state
divergence**: when `max_uncommitted_size = 0` (no limit), the Lean model increments
`uncommittedSize` but the Rust implementation returns early without updating it.  The
boolean return value agrees on all 13 test cases; no proved theorem depends on the
divergent state.  See `CRITIQUE.md §Run 110` for the full analysis.

## Proof Bridges (Run 92)

| ID | File | Theorems | Status | Key contribution |
|----|------|---------|--------|-----------------|
| UPB1–UPB8 | `FVSquad/UnstablePersistBridge.lean` | 8 | ✅ proved, 0 sorry | Bridges `LogUnstable.wf` invariant → `MaybePersistFUI` safety (UPB8: if `wf u` and advance succeeds, `newPersisted < u.offset`) |

## Next Steps

The priority order for future runs, given the current state (Run 111):

1. **Task 5 (Proof Assistance)**: Connect `ElectionBroadcastChain` to `RaftReachable` to discharge
   `HLogConsistency` unconditionally — the last major abstract gap in the protocol-level safety proof.
2. **Task 8 Route B**: Correspondence tests for `has_next_entries_since` (new target, Run 111).
3. **Task 7 (Critique)**: Update `CRITIQUE.md` with Runs 109–111.
4. **Task 10 (Report)**: Update `REPORT.md` with Runs 109–111 (647T→661T, 67→68 files).
5. **Task 11 (Conference Paper)**: Update `paper.tex` with Run 110–111 results.
6. **Task 5 (ProgressTracker integration)**: Connect PT1–PT24 to leader-init theorem.

*(Run 103: Added `ConfigurationInvariantsCorrespondence.lean` (15 `#guard`) and
`test_configuration_invariants_correspondence` in `src/tracker.rs`. TARGETS.md updated to
reflect 626+ theorems, 65 Lean files, 22 correspondence test targets, ~442 `#guard` total.)*

---

## ECM Gap Progress (Runs 43–46)

**Status after Run 46**: `hqc_preserved` is now closed from the `hae` (log-agreement) hypothesis.
The remaining concrete gap is deriving `hae` inductively.

| File | Theorems | Status | Key contribution |
|------|---------|--------|-----------------|
| `FVSquad/ElectionReachability.lean` | 12 (ER1–ER12) | ✅ proved, 0 sorry | Shared-source → CandidateLogCovers |
| `FVSquad/ElectionConcreteModel.lean` | 8 (ECM1–ECM7) | ✅ proved, 0 sorry | hqc_preserved from hae (ECM6) |
| `FVSquad/RaftLogAppend.lean` | 14 (RA1–RA9+3) | ✅ Phase 4, 0 sorry | append spec + P4/P5 prefix preservation |

### New target: `hae_inductive` (Phase 1 — Research)

**Goal**: Prove `HAEInvariant cs lead` as an inductive invariant over a sequence of
concrete Raft steps. This invariant states:

```lean
def HAEInvariant (cs : ClusterState E) (lead : Nat) (voterLog : Nat → LogId) :=
  ∀ w k, k ≤ (voterLog w).index → cs.logs w k = cs.logs lead k
```

**Proof path**:
1. Show `HAEInvariant` holds after the leader broadcasts AE to all voters and all accept.
2. Show `HAEInvariant` is preserved by further `ValidAEStep` applications (ECM5 seeds this).
3. Compose with ECM6 to get `hqc_preserved` without `hae` as an explicit precondition.

**Approximate new theorems needed**: 10–20 in a new file `AEBroadcastInvariant.lean`.

**Difficulty**: Medium — the inductive structure is clear from ECM5; the main challenge
is formalising "all voters have accepted" as a model-level predicate.

| Priority | ID | Proposed file | Goal | Phase | Difficulty |
|----------|----|--------------|------|-------|-----------|
| **A6** | `hae_inductive` | `FVSquad/AEBroadcastInvariant.lean` | Inductive `hae` across AE history | 1 | Medium |

---

## ER Gap Progress (Run 43+)

**`ElectionReachability.lean`** (new file) bridges abstract election conditions to `CandidateLogCovers`:

| File | Theorems | Status |
|------|---------|--------|
| `FVSquad/ElectionReachability.lean` | 12 (ER1–ER12) | ✅ proved, 0 sorry |

The file derives `CandidateLogCovers` from concrete election conditions:

| Theorem | Statement | Chain level |
|---------|-----------|------------|
| ER1 | HWM + CandLogMatching → CandLogCoversLastIndex | Foundation |
| ER2 | HWM + CandLogMatching → HLogConsistency | HLogConsistency bridge |
| ER3 | HWM + VRC + voterIdx → CandidateLogCovers | CandidateLogCovers bridge |
| ER4 | HWM + VRC + voterIdx + DecidableEq → leaderCompleteness | End-to-end |
| ER5 | Extended LMI + hcand_eq → CandLogMatching | LMI → CandLogMatching |
| ER6 | Shared entry at j ≥ voterIdx → HWM | HWM from agreement |
| ER7 | LMI + agreement at voterIdx → HWM | LMI → HWM |
| ER8 | Extended LMI + hcand_eq + HWM + VRC → CandidateLogCovers | Full chain |
| ER9 | Shared source log R → CandLogCoversLastIndex | Shared-source reduction |
| ER10 | Shared source → CandidateLogCovers | Shared-source → top |
| ER11 | Shared source + DecidableEq → leaderCompleteness | End-to-end (shared) |
| ER12 | AE prefix preservation: prior agreements survive AE step | Inductive invariant |

**Remaining gap** (after ECM, Runs 43–46): The concrete proof obligation reduces to
showing that the `hae` invariant holds inductively across the AE broadcast history.
ECM5 gives it for a single step. The `AEBroadcastInvariant.lean` target (A6) closes this.

**lakefile.toml**: added `globs = ["FVSquad.+*"]` so all modules are included in `lake build`.

---

## A5 Gap Progress (Run 38+)

**`ConcreteProtocolStep.lean`** (new file, this run) provides the A5 bridge:

| File | Theorems | Status |
|------|---------|--------|
| `FVSquad/ConcreteProtocolStep.lean` | 13 (CPS1–CPS12 + example) | ✅ proved, 0 sorry |

The file defines `ValidAEStep` — a structure capturing the concrete AppendEntries
preconditions — and proves that it satisfies all five `RaftReachable.step` hypotheses.

| `step` hypothesis | Discharged by |
|------------------|--------------|
| `hlogs'`         | `ValidAEStep.hlogs'_other` |
| `hno_overwrite`  | CPS1 (`h_committed_le_prev` + CT2) |
| `hqc_preserved`  | CPS13 (`validAEStep_hqc_preserved_from_lc`) |
| `hcommitted_mono`| `ValidAEStep.hcommitted_mono` (explicit) |
| `hnew_cert`      | `ValidAEStep.hnew_cert` (explicit, needs CommitRuleValid) |

**Run 46: ElectionConcreteModel.lean** — closes the `hqc_preserved` gap (8 theorems):

| File | Theorems | Status |
|------|---------|--------|
| `FVSquad/ElectionConcreteModel.lean` | 8 (ECM1–ECM7) | ✅ proved, 0 sorry |

The file proves `hqc_preserved` from the **shared-source hypothesis** `hae`:

| Theorem | Role |
|---------|------|
| ECM1 (`candLogCoversLastIndex_of_hae`) | ER9 with R = candLog — trivial from hae |
| ECM2 (`candLogMatching_of_hae`) | CT5 with hae + hlog_none + hcand_mono |
| ECM3 (`candidateLogCovers_of_hae`) | ER10 = ECM1 + ECM2 + hconsist |
| ECM4 (`hqc_preserved_of_hae`) | CPS13 ∘ ECM3 |
| ECM5 (`hae_of_validAEStep`) | Single AE step gives voter ≡ leader at new indices |
| ECM6 (`hqc_preserved_of_validAEStep`) | Complete bridge: hae + ValidAEStep → hqc_preserved |
| ECM7 (`sharedSource_of_hae`) | Explicit shared-source witness (R = candLog) |
