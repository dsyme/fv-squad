# FV Targets — `raft-rs`

> 🔬 *Lean Squad — prioritised formal verification target list.*

| Priority | Target | File(s) | Phase | Status | Notes |
|----------|--------|---------|-------|--------|-------|
| 1 | `majority` + `MajorityConfig::vote_result` | `src/util.rs`, `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). See `FVSquad/MajorityQuorum.lean`. |
| 2 | `MajorityConfig::committed_index` | `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). Bridge lemma `countGe_eq_sorted_countP` completed the `committedIndex_safety` and `committedIndex_maximal` proofs. See `FVSquad/CommittedIndex.lean`. |
| 3 | `Unstable` log buffer | `src/log_unstable.rs` | 5 — Proofs | ✅ Done | All key theorems proved (0 `sorry`): `truncateAndAppend_wellFormed`, `stableEntries_wellFormed`, `stableSnap_wellFormed`. See `FVSquad/UnstableLog.lean`. |
| 4 | `Inflights` ring buffer | `src/tracker/inflights.rs` | 5 — Proofs | ✅ Done | Abstract model fully proved (0 `sorry`): 20+ theorems. Concrete ring-buffer model added with `concreteAdd_abstract`, `ring_pos_ne`. See `FVSquad/Inflights.lean`. |
| 5 | `limit_size` utility | `src/util.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). See `FVSquad/LimitSize.lean`. |
| 6 | `Progress` state machine | `src/tracker/progress.rs`, `src/tracker/state.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). ~45 theorems including master invariant `valid_preserved_by_all_ops`. See `FVSquad/Progress.lean`. |
| 7 | `JointConfig` joint quorum | `src/quorum/joint.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). 20+ theorems covering `jointVoteResult` and `jointCommittedIndex` safety/monotonicity. See `FVSquad/JointQuorum.lean`. |
| 8 | `is_up_to_date` + `find_conflict_by_term` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 16 theorems, 0 `sorry`. See `FVSquad/LogOrdering.lean`. |
| 9 | `RaftLog::maybe_append` + `maybe_commit` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | All sorrys removed. See `FVSquad/MaybeAppend.lean`. |
| 10 | `ReadOnly` queue (ReadIndex protocol) | `src/read_only.rs` | 5 — Proofs | ✅ Done | All 30 theorems proved (0 `sorry`). See `FVSquad/ReadOnly.lean`. |
| 11 | `RaftLog::maybe_persist` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 16 theorems, 0 `sorry`. WF preserved. See `FVSquad/MaybePersist.lean`. |
| 12 | `RaftLog::maybe_commit` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 16 theorems, 0 `sorry`. See `FVSquad/MaybeCommit.lean`. |
| 13 | `Progress::maybe_update` / `update_committed` / `maybe_decr_to` | `src/tracker/progress.rs` | 5 — Proofs | ✅ Done | 31 theorems, 0 `sorry`. See `FVSquad/ProgressTracking.lean`. |
| 14 | `ProgressTracker::quorum_recently_active` | `src/tracker.rs` | 5 — Proofs | ✅ Done | 15 theorems, 0 `sorry`. See `FVSquad/QuorumRecentlyActive.lean`. |
| 15 | `RaftLog::next_entries_since` + `applied_index_upper_bound` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 20+ theorems, 0 `sorry`. See `FVSquad/NextEntries.lean`. |
| 16 | `RaftLog::append` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 14 theorems, 0 `sorry`. See `FVSquad/RaftLogAppend.lean`. |
| 17 | `RaftLog::entries` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 18 theorems, 0 `sorry`. See `FVSquad/RaftLogEntries.lean`. |
| 18 | `RaftLog::slice` + `must_check_outofbounds` | `src/raft_log.rs`, `src/log_unstable.rs` | 5 — Proofs | ✅ Done | 35+ theorems, 0 `sorry`. See `FVSquad/RaftLogSlice.lean`. |
| 19 | `Config::validate` | `src/config.rs` | 5 — Proofs | ✅ Done | 18 theorems, 0 `sorry`. See `FVSquad/ConfigValidate.lean`. |
| 20 | `UncommittedState` | `src/raft.rs` | 5 — Proofs | ✅ Done | 28 theorems, 0 `sorry`. See `FVSquad/UncommittedState.lean`. |
| 21 | `RaftLog::term` + `match_term` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 18 theorems, 0 `sorry`. See `FVSquad/RaftLogTerm.lean`. |
| 22 | `RaftLog::restore` | `src/raft_log.rs` | 5 — Proofs | ✅ Done | 12 theorems, 0 `sorry`. See `FVSquad/RaftLogRestore.lean`. |
| 23 | `tally_votes` + `has_quorum` | `src/tracker.rs` | 5 — Proofs | ✅ Done | 27 theorems, 0 `sorry`. See `FVSquad/TallyVotes.lean`. |
| 24 | `Union<'a>` + `is_continuous_ents` | `src/util.rs` | 5 — Proofs | ✅ Done | 20 theorems, 0 `sorry`. See `FVSquad/UnionUtils.lean`. |
| 25 | `Changer::enter_joint` / `leave_joint` / `check_invariants` | `src/confchange/changer.rs` | 5 — Proofs | ✅ Done | 26 propositions, 0 `sorry`. See `FVSquad/ConfChanger.lean`. |
| 26 | `to_conf_change_single` + `restore` | `src/confchange/restore.rs` | 5 — Proofs | ✅ Done | 12 abstract props + 7 phase-5 theorems (IMPL-1–7). Full non-joint round-trip proved: `restore_nonJoint_voters`. 0 `sorry`. See `FVSquad/ConfChangeRestore.lean`. |
| 30 | `become_leader` / `become_follower` / `become_candidate` state transitions | `src/raft.rs` | 5 — Proofs | ✅ Done | 31 theorems, 0 `sorry`. Term monotonicity, self-vote, state role transitions, election cycle. See `FVSquad/StateTransitions.lean`. |
| 27 | `is_local_msg` + `is_response_msg` + `vote_resp_msg_type` | `src/raw_node.rs`, `src/raft.rs` | 5 — Proofs | ✅ Done | 13 theorems, 0 `sorry`. MsgUnreachable overlap proved. See `FVSquad/MsgType.lean`. |
| 28 | `get_priority` | `src/raft.rs` | 5 — Proofs | ✅ Done | Priority selection with u64→i64 overflow-safe fallback. 10 propositions, 0 `sorry`. See `FVSquad/GetPriority.lean`. |
| 29 | `vote_commitment` | `src/raft.rs` | 5 — Proofs | ✅ Done | Raft vote-commitment invariant: at most one vote per term. 15 propositions, 0 `sorry`. See `FVSquad/VoteCommitment.lean`. |
| 31 | `bcast_append` / `maybe_send_append` / `prepare_send_entries` | `src/raft.rs`, `src/tracker/progress.rs` | 5 — Proofs | ✅ Done | Flow-control, progress state machine, MsgAppend fields. 11+ theorems, 0 `sorry`. See `FVSquad/BcastAppend.lean`. |
| 32 | `handle_heartbeat_response` | `src/raft.rs` | 5 — Proofs | ✅ Done | Progress unblocking, catch-up trigger, ReadIndex quorum. Full `handleHeartbeatResponse` pure model + 8 end-to-end theorems, 0 `sorry`. See `FVSquad/HandleHeartbeatResponse.lean`. |
| 33 | `handle_vote` (MsgRequestVote / MsgRequestPreVote) | `src/raft.rs` | 5 — Proofs | ✅ Done | Vote grant conditions (`canVote`, `isUpToDate`, `priorityOk`), 19 theorems, 0 `sorry`. Full pure model + proofs. See `FVSquad/HandleVote.lean`. |
| 34 | `handle_append_entries` | `src/raft.rs` | 5 — Proofs | ✅ Done | 3 paths: snapshot-pending, stale, accept/reject. 14 theorems, 0 `sorry`. See `FVSquad/HandleAppendEntries.lean`. |
| 35 | `tick_election` | `src/raft.rs` | 5 — Proofs | ✅ Done | Election timer logic: 10+ theorems, 0 `sorry`. Pure model + full proofs P1–P8 + derived. See `FVSquad/TickElection.lean`. |
| 36 | `maybe_commit_by_vote` | `src/raft.rs` | 5 — Proofs | ✅ Done | Fast-forward commit during election. 15 theorems, 0 `sorry`. commit_monotone, stepdown safety, idempotency. See `FVSquad/MaybeCommitByVote.lean`. |
| 37 | `handle_append_response` | `src/raft.rs` | 5 — Proofs | ✅ Done | Leader-side handling of MsgAppendResponse: progress tracking, backtracking optimisation, commit advancement, leadership transfer. 15 theorems, 0 sorry. `FVSquad/HandleAppendResponse.lean` |
| 38 | `restore` (node-level) | `src/raft.rs` | 5 — Proofs | ✅ Done | 20 theorems, 0 `sorry`. 5 paths: StaleSnapshot/NonFollower/NotInConfig/FastForward/FullRestore. Commit-monotone, term-monotone, state-follower, pendingReqSnap cleared. See `FVSquad/RestoreNode.lean`. |
| 39 | `handle_snapshot_status` | `src/raft.rs` | 5 — Proofs | ✅ Done | Snapshot→Probe transition: 13 theorems, 0 `sorry`. Success/failure paths, next_idx correctness, pause semantics. See `FVSquad/HandleSnapshotStatus.lean`. |
| 40 | `RawNode::has_ready` | `src/raw_node.rs` | 3 — Lean Spec | 🔄 In progress | 7-condition disjunctive predicate. `hasReady_iff` + 9 component theorems. See `FVSquad/HasReady.lean`. |
| 41 | `commit_to_current_term` / `apply_to_current_term` | `src/raft.rs` | 5 — Proofs | ✅ Done | Liveness gate predicates for leader reads. 17 theorems, 0 `sorry`. Key theorem: `applyImpliesCommit` (under log monotonicity + term boundedness). See `FVSquad/CommitCurrentTerm.lean`. |
| 42 | `RaftCore::reset` | `src/raft.rs` | 1 — Research | ⬜ Not started | Term-change state reset; postconditions: term mono, vote cleared, elapsed zeroed. |

## Phase Legend

| Phase | Description |
|-------|-------------|
| 1 | Research — target identified, approach documented |
| 2 | Informal Spec — `specs/<name>_informal.md` written |
| 3 | Lean Spec — Lean 4 types + propositions (with `sorry`) |
| 4 | Implementation — Lean model of the Rust implementation |
| 5 | Proofs — `sorry`s removed, theorems fully proved |
