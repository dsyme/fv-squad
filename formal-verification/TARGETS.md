# FV Targets

> 🔬 *Lean Squad — automated formal verification for this repository.*

Prioritised target list. Phases: 1=Research, 2=Informal Spec, 3=Lean Spec, 4=Lean Impl, 5=Proofs.

| Priority | ID | File | Function | Phase | Notes |
|----------|----|------|----------|-------|-------|
| 1 | `limit_size` | `src/util.rs` | `limit_size` | 5 ✅ | All 12 theorems proved (0 sorry). `FVSquad/LimitSize.lean`. |
| 2 | `config_validate` | `src/config.rs` | `Config::validate` | 5 ✅ | All 10 theorems proved (0 sorry). `FVSquad/ConfigValidate.lean`. |
| 3 | `vote_result` | `src/quorum/majority.rs` | `Configuration::vote_result` | 5 ✅ | 21 theorems proved (0 sorry). `FVSquad/MajorityVote.lean`. |
| 4 | `committed_index` | `src/quorum/majority.rs` | `Configuration::committed_index` | 5 ✅ | ALL 13 theorems proved (0 sorry). Safety, maximality, monotonicity all proved. `FVSquad/CommittedIndex.lean`. |
| 5 | `find_conflict` | `src/raft_log.rs` | `RaftLog::find_conflict` | 2 | First term mismatch scan. Informal spec at `specs/find_conflict_informal.md`. |
| 6 | `maybe_append` | `src/raft_log.rs` | `RaftLog::maybe_append` | 1 | Depends on `find_conflict`. |
| 7 | `joint_vote_result` | `src/quorum/joint.rs` | `JointConfig::vote_result` | 5 ✅ | 14 theorems proved (0 sorry). `FVSquad/JointVote.lean`. Builds on `MajorityVote`. |
| 8 | `joint_committed_index` | `src/quorum/joint.rs` | `JointConfig::committed_index` | 1 | Depends on `committed_index`. |
| 9 | `inflights` | `src/tracker/inflights.rs` | ring buffer ops | 1 | Ring buffer invariants. |
| 10 | `progress` | `src/tracker/progress.rs` | state machine | 1 | Progress state machine transitions. |

## Next Steps

1. **Task 3+4+5** (Lean Spec+Impl+Proofs for `find_conflict`) — informal spec at `specs/find_conflict_informal.md`; P1–P8 are all induction-on-list and should close easily.
2. **Task 2+3+4+5** (Spec+Impl+Proofs for `maybe_append`) — depends on `find_conflict`; higher complexity due to mutable log state.
3. **Task 2+3+4+5** (Spec+Impl+Proofs for `joint_committed_index`) — thin shim over proved `committedIndex`; fast win.
4. **Task 8** (Aeneas extraction) — blocked on OCaml/opam in no-new-privileges containers.
