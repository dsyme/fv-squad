# FV Targets

> 🔬 *Lean Squad — automated formal verification for this repository.*

Prioritised target list. Phases: 1=Research, 2=Informal Spec, 3=Lean Spec, 4=Lean Impl, 5=Proofs.

| Priority | ID | File | Function | Phase | Notes |
|----------|----|------|----------|-------|-------|
| 1 | `limit_size` | `src/util.rs` | `limit_size` | 2 | Informal spec written. Pure list truncation. Very high tractability. |
| 2 | `config_validate` | `src/config.rs` | `Config::validate` | 1 | Decidable arithmetic constraints. Very high tractability. |
| 3 | `vote_result` | `src/quorum/majority.rs` | `Configuration::vote_result` | 1 | Majority quorum. Aeneas-safe variant available. |
| 4 | `committed_index` | `src/quorum/majority.rs` | `Configuration::committed_index` | 1 | Sort-then-index quorum commit. Aeneas-safe variant. |
| 5 | `find_conflict` | `src/raft_log.rs` | `RaftLog::find_conflict` | 1 | First term mismatch scan. |
| 6 | `maybe_append` | `src/raft_log.rs` | `RaftLog::maybe_append` | 1 | Depends on `find_conflict`. |
| 7 | `joint_vote_result` | `src/quorum/joint.rs` | `JointConfig::vote_result` | 1 | Depends on `vote_result`. |
| 8 | `joint_committed_index` | `src/quorum/joint.rs` | `JointConfig::committed_index` | 1 | Depends on `committed_index`. |
| 9 | `inflights` | `src/tracker/inflights.rs` | ring buffer ops | 1 | Ring buffer invariants. |
| 10 | `progress` | `src/tracker/progress.rs` | state machine | 1 | Progress state machine transitions. |

## Next Steps

1. **Task 3** (Lean Spec for `limit_size`) — blocked on Lean toolchain availability (network firewall in CI).
2. **Task 3** (Lean Spec for `config_validate`) — same blocker.
3. **Task 8** (Aeneas extraction for `vote_result` / `committed_index`) — blocked on Charon+Aeneas build.
4. Once CI has network access, all Lean work can proceed.
