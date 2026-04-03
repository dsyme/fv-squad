# FV Targets

> 🔬 *Lean Squad — automated formal verification for this repository.*

Prioritised target list. Phases: 1=Research, 2=Informal Spec, 3=Lean Spec, 4=Lean Impl, 5=Proofs.

| Priority | ID | File | Function | Phase | Notes |
|----------|----|------|----------|-------|-------|
| 1 | `limit_size` | `src/util.rs` | `limit_size` | 5 ✅ | All 12 theorems proved (0 sorry). `FVSquad/LimitSize.lean`. |
| 2 | `config_validate` | `src/config.rs` | `Config::validate` | 5 ✅ | All 10 theorems proved (0 sorry). `FVSquad/ConfigValidate.lean`. |
| 3 | `vote_result` | `src/quorum/majority.rs` | `Configuration::vote_result` | 5 ✅ | 21 theorems proved (0 sorry). `FVSquad/MajorityVote.lean`. |
| 4 | `committed_index` | `src/quorum/majority.rs` | `Configuration::committed_index` | 5 ✅ | ALL 17 theorems proved (0 sorry). Safety, maximality, monotonicity all proved. `FVSquad/CommittedIndex.lean`. |
| 5 | `find_conflict` | `src/raft_log.rs` | `RaftLog::find_conflict` | 5 ✅ | ALL 12 theorems proved (0 sorry). `FVSquad/FindConflict.lean`. |
| 6 | `maybe_append` | `src/raft_log.rs` | `RaftLog::maybe_append` | 4 ✅ | 18 theorems proved (0 sorry). `FVSquad/MaybeAppend.lean`. Tasks 3+4 done: spec + impl model including `logWithEntries`, `applyConflict`. MA1–MA16. |
| 7 | `joint_vote_result` | `src/quorum/joint.rs` | `JointConfig::vote_result` | 5 ✅ | 14 theorems proved (0 sorry). `FVSquad/JointVote.lean`. Builds on `MajorityVote`. |
| 8 | `joint_committed_index` | `src/quorum/joint.rs` | `JointConfig::committed_index` | 5 ✅ | 10 theorems proved (0 sorry). `FVSquad/JointCommittedIndex.lean`. Builds on `CommittedIndex`. |
| 9 | `inflights` | `src/tracker/inflights.rs` | ring buffer ops | 5 ✅ | 49 theorems proved (0 sorry). Abstract (`Inflights`) + concrete (`InflightsConc`) ring-buffer model. All correspondence theorems proved. `FVSquad/Inflights.lean`. |
| 10 | `progress` | `src/tracker/progress.rs` | state machine | 5 ✅ | 31 theorems proved (0 sorry). State machine transitions, `wf` invariant (`matched+1≤next_idx`), `maybeUpdate`, `isPaused`, `maybeDecrTo`. `FVSquad/Progress.lean`. |
| 11 | `progress_set` | `src/tracker/progress_set.rs` | quorum tracking | 1 | Next target: quorum tracking over the progress map. |
| 12 | `is_up_to_date` | `src/raft_log.rs` | log freshness comparison | 5 ✅ | 18 theorems proved (0 sorry). Reflexivity, totality, transitivity, antisymmetry of log order. `FVSquad/IsUpToDate.lean`. |
| 13 | `log_unstable` | `src/log_unstable.rs` | unstable log segment ops | 5 ✅ | 37 theorems proved (0 sorry). All query ops, state transitions, wf invariant, truncate_and_append 3-case analysis. `FVSquad/LogUnstable.lean`. |
| 14 | `tally_votes` | `src/tracker.rs` | `ProgressTracker::tally_votes` | 5 ✅ | 18 theorems proved (0 sorry). Granted/rejected counting, partition identity, rejection-closes-election safety property, all/none voting lemmas. `FVSquad/TallyVotes.lean`. |
| 15 | `has_quorum` | `src/tracker.rs` | `ProgressTracker::has_quorum` | 5 ✅ | 22 theorems proved (0 sorry). Quorum intersection / Raft safety property (HQ14, HQ20). `FVSquad/HasQuorum.lean`. |
| 16 | `quorum_recently_active` | `src/tracker.rs` | `ProgressTracker::quorum_recently_active` | 5 ✅ | 15 theorems proved (0 sorry). Leader always active (QRA4), monotonicity, nil-entries/nil-voters edge cases, singleton-self quorum. `FVSquad/QuorumRecentlyActive.lean`. |
| 17 | `safety_composition` | cross-module | `committedIndex` × `hasQuorum` × `quorumRecentlyActive` | 5 ✅ | 9 theorems proved (0 sorry). Raft log safety (SC4), biconditional quorum↔committedIndex (SC6), leader election safety (SC9). `FVSquad/SafetyComposition.lean`. |
| 18 | `joint_tally` | `src/tracker.rs` | `ProgressTracker::tally_votes` (joint) | 5 ✅ | 14 theorems proved (0 sorry). Joint-quorum extension of tally_votes: Won/Lost/Pending iff, non-joint degeneration (JT5), symmetry of Won (JT13). `FVSquad/JointTally.lean`. |
| 19 | `joint_safety_composition` | cross-module | `jointCommittedIndex` × `hasQuorum` × `SafetyComposition` | 5 ✅ | 10 theorems proved (0 sorry). Joint Raft log-safety certificate (JSC7): witnesses in both incoming and outgoing halves. Extends SC4 to joint-config. `FVSquad/JointSafetyComposition.lean`. |
| 20 | `raft_protocol` | `src/raft_log.rs` + `proto/` | AppendEntries / RequestVote transitions | 3 ✅ | 6 theorems proved (0 sorry), 2 sorry (RP6, RP8). `FVSquad/RaftProtocol.lean`. Message types, LogMatchingInvariant, NoRollbackInvariant. Bridges to RSS3/RSS4. |
| 21 | `progress_set` | `src/tracker/progress_set.rs` | quorum tracking over progress map | 1 | Next: formalise `ProgressSet::quorum_active` and quorum detection across the voter progress map. |
| 22 | `raft_log_append` | `src/raft_log.rs` | `RaftLog::append` | 1 | Candidate: append correctness and slice invariants for the stable log. |

## Next Steps

1. **Target 20** (`raft_protocol`) — prove RP6 (AppendEntries preserves log matching) and RP8 (valid transitions satisfy no-rollback). Requires introducing a `RaftTrace` inductive type.
2. **Target 21** (`progress_set`) — formalise quorum tracking over the `ProgressSet` map: `quorum_active`, voter iteration, and its connection to `hasQuorum`.
3. **RSS3/RSS4** — once RP6 and RP8 are proved, RSS3 and RSS4 follow via `rss3_from_logMatchInvariant` and `rss4_from_noRollback`.
4. **Task 8** (Aeneas extraction) — blocked on OCaml/opam in no-new-privileges containers.
