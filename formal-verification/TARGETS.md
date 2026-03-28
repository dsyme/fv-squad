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
| 9 | `inflights` | `src/tracker/inflights.rs` | ring buffer ops | 1 | **Research done (run110).** FIFO ring buffer: `add`, `free_to`, `free_first_one`, `reset`. Key FV targets: (a) `count ≤ cap` invariant, (b) `free_to` correctness, (c) `add` content property. Model: abstract as ordered sequence. Medium tractability. |
| 10 | `progress` | `src/tracker/progress.rs` | state machine | 1 | Progress state machine transitions. |

## Next Steps

1. **Task 5** (Proofs for `maybe_append`) — implementation model done; prove stronger log-content theorems for `maybe_append`; specifically MA13+ with more explicit consecutive-indexing assumptions.
2. **Task 2** (Informal Spec for `inflights`) — ring buffer with wrap-around; medium complexity. Research done (run110).
3. **Task 8** (Aeneas extraction) — blocked on OCaml/opam in no-new-privileges containers.
