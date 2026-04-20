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

## Active / Future Targets — Closing the Election Model Gap

An external critique (2026-04-20) identified that `RaftReachable.step` bundles 5 hypotheses
as abstract axioms.  The following targets are **required to make the proof fully self-contained**.
See `CRITIQUE.md §Critical Gap Analysis` for the full analysis.

| Priority | ID | Proposed file | Goal | Phase | Difficulty | Gap addressed |
|----------|----|--------------|------|-------|-----------|---------------|
| **A1** | `election_model` | `FVSquad/RaftElection.lean` | Model `NodeState` (currentTerm, votedFor, role), vote-granting rules, term monotonicity | 1 | Medium | All 5 step hypotheses (foundation) |
| **A2** | `election_safety` | `FVSquad/RaftElection.lean` | Prove at most one leader per term (ElectionSafety); uses HQ20 + TallyVotes | 1 | Medium-high | `hqc_preserved` (partial) |
| **A3** | `leader_completeness` | `FVSquad/LeaderCompleteness.lean` | Compose HQ20 + IU16 + RSS5: elected leader has all quorum-certified entries | 1 | **High** | `hqc_preserved` (full discharge) |
| **A4** | `concrete_transitions` | `FVSquad/ConcreteRaft.lean` | AppendEntries + RequestVote with terms; discharge `hlogs'`, `hno_overwrite`, `hcommitted_mono` | 1 | Medium | 3 of 5 step hypotheses |
| **A5** | `commit_rule` | `FVSquad/ConcreteRaft.lean` | Discharge `hnew_cert` — commit only after quorum ACK; builds on CMC3 | 1 | Medium-high | `hnew_cert` |

## Other Pending Targets

| Priority | ID | File | Function | Phase | Notes |
|----------|----|------|----------|-------|-------|
| 11 | `progress_set` | `src/tracker/progress_set.rs` | quorum tracking over progress map | 1 | Formalise `ProgressSet::quorum_active` and quorum detection across the voter progress map. |
| 22 | `raft_log_append` | `src/raft_log.rs` | `RaftLog::append` | 4 ✅ | Lean spec + impl extraction (Run 45+46). `FVSquad/RaftLogAppend.lean` (14 theorems: RA1–RA9 + taa_entries_nonempty + taa_maybeLastIndex + taa_maybeTerm_before + ra_prefix_preserved + ra_committed_prefix_preserved). P4/P5 prefix-preservation proved (Run 46). |

## Next Steps

The priority order for future runs, given the critique:

1. **A1: Election model** (`RaftElection.lean`) — the foundation for all other gap targets.
   Define `NodeState`, vote-granting rule, term monotonicity, message-delivery model.
2. **A2: ElectionSafety** — prove at most one leader per term using HQ20 + TallyVotes composition.
3. **A3: LeaderCompleteness** — the hardest gap: compose HQ20 + IU16 + RSS5 to prove that
   election winners have all committed entries; this discharges `hqc_preserved`.
4. **A4+A5: ConcreteTransitions + CommitRule** — discharge the remaining 4 step hypotheses.
5. **Target 11** (`progress_set`) — lower priority than closing the election model gap.
6. **Task 8** (Aeneas extraction) — blocked on OCaml/opam in no-new-privileges containers.

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

**Remaining gap**: `hqc_preserved` still needs `CandLogMatching` and the `HWM` condition
to be derived from the concrete election protocol state. `ER5` and `ER6/ER7` reduce this
to showing that log-matching holds between the candidate and voters at the vote index.

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
