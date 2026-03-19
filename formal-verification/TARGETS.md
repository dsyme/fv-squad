# FV Targets — `raft-rs`

> 🔬 *Lean Squad — prioritised formal verification target list.*

| Priority | Target | File(s) | Phase | Status | Notes |
|----------|--------|---------|-------|--------|-------|
| 1 | `majority` + `MajorityConfig::vote_result` | `src/util.rs`, `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). See `FVSquad/MajorityQuorum.lean`. |
| 2 | `MajorityConfig::committed_index` | `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). Bridge lemma `countGe_eq_sorted_countP` completed the `committedIndex_safety` and `committedIndex_maximal` proofs. See `FVSquad/CommittedIndex.lean`. |
| 3 | `Unstable` log buffer | `src/log_unstable.rs` | 5 — Proofs | ✅ Done | All key theorems proved (0 `sorry`): `truncateAndAppend_wellFormed`, `stableEntries_wellFormed`, `stableSnap_wellFormed`. See `FVSquad/UnstableLog.lean`. |
| 4 | `Inflights` ring buffer | `src/tracker/inflights.rs` | 5 — Proofs | ✅ Done | Abstract model fully proved (0 `sorry`): 20+ theorems. Concrete ring-buffer model added with `concreteAdd_abstract`, `ring_pos_ne`. See `FVSquad/Inflights.lean`. |
| 5 | `limit_size` utility | `src/util.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). Budget helpers `limitSizeGo_count_add`, `limitSizeGo_budget'`, `limitSizeGo_stop_condition` enable proofs of `limitSize_sum_le` (budget safety) and `limitSize_maximal` (maximality). See `FVSquad/LimitSize.lean`. |
| 6 | `Progress` state machine | `src/tracker/progress.rs`, `src/tracker/state.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). ~45 theorems including master invariant `valid_preserved_by_all_ops`. See `FVSquad/Progress.lean`. |
| 7 | `JointConfig` joint quorum | `src/quorum/joint.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). 20+ theorems covering `jointVoteResult` and `jointCommittedIndex` safety/monotonicity. See `FVSquad/JointQuorum.lean`. |

| 8 | `is_up_to_date` + `find_conflict_by_term` | `src/raft_log.rs` | 4 — Implementation | 🔄 In progress | Informal spec written. Lean 4 spec + implementation model: `isUpToDate` (total preorder, 7 theorems), `findConflictByTerm` (structural recursion, 9 theorems incl. maximality). 0 `sorry`. See `FVSquad/LogOrdering.lean`. |
| 9 | `RaftLog::maybe_append` + `maybe_commit` | `src/raft_log.rs` | 1 — Research | ⬜ Not started | New target identified this run. Key properties: commit monotonicity, append validity, no-truncate-committed. See `RESEARCH.md` Target 9. |

## Phase Legend

| Phase | Description |
|-------|-------------|
| 1 | Research — target identified, approach documented |
| 2 | Informal Spec — `specs/<name>_informal.md` written |
| 3 | Lean Spec — Lean 4 types + propositions (with `sorry`) |
| 4 | Implementation — Lean model of the Rust implementation |
| 5 | Proofs — `sorry`s removed, theorems fully proved |
