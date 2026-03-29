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
| 6 | `maybe_append` | `src/raft_log.rs` | `RaftLog::maybe_append` | 5 ✅ | 18 theorems proved (0 sorry). `FVSquad/MaybeAppend.lean`. Tasks 3+4+5 done: spec, impl model, MA1–MA16 all proved. |
| 7 | `joint_vote_result` | `src/quorum/joint.rs` | `JointConfig::vote_result` | 5 ✅ | 14 theorems proved (0 sorry). `FVSquad/JointVote.lean`. Builds on `MajorityVote`. |
| 8 | `joint_committed_index` | `src/quorum/joint.rs` | `JointConfig::committed_index` | 5 ✅ | 10 theorems proved (0 sorry). `FVSquad/JointCommittedIndex.lean`. Builds on `CommittedIndex`. |
| 9 | `inflights` | `src/tracker/inflights.rs` | ring buffer ops | 3 ✅ | Informal spec + Lean spec done (run111). 15 theorems proved (0 sorry). `FVSquad/Inflights.lean`. INF1–INF15: count/cap, add, freeTo, freeFirstOne, reset. |
| 10 | `progress` | `src/tracker/progress.rs` | state machine | 1 | Progress state machine transitions. |

## Next Steps

1. **Task 4+5** (Implementation + Proofs for `inflights`) — phase 3 done (run111); next add implementation model and prove stronger theorems (ring buffer semantics, prefix freeing).
2. **Task 2** (Informal Spec for `progress`) — state machine transitions in `src/tracker/progress.rs`.
3. **Task 8** (Aeneas extraction) — blocked on OCaml/opam in no-new-privileges containers.
