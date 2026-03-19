# FV Targets — `raft-rs`

> 🔬 *Lean Squad — prioritised formal verification target list.*

| Priority | Target | File(s) | Phase | Status | Notes |
|----------|--------|---------|-------|--------|-------|
| 1 | `majority` + `MajorityConfig::vote_result` | `src/util.rs`, `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). See `FVSquad/MajorityQuorum.lean`. |
| 2 | `MajorityConfig::committed_index` | `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). Bridge lemma `countGe_eq_sorted_countP` completed the `committedIndex_safety` and `committedIndex_maximal` proofs. See `FVSquad/CommittedIndex.lean`. |
| 3 | `Unstable` log buffer | `src/log_unstable.rs` | 5 — Proofs | 🔄 In progress | Informal spec + Lean spec + impl model + wellFormed preservation theorems. `truncateAndAppend_wellFormed`, `stableEntries_wellFormed`, `stableSnap_wellFormed` proved. 0 `sorry`. See `FVSquad/UnstableLog.lean`. |
| 4 | `Inflights` ring buffer | `src/tracker/inflights.rs` | 5 — Proofs | 🔄 In progress | Informal spec + Lean 4 abstract model (0 `sorry`): 20+ theorems proved (incl. `freeTo_all_gt`, `freeTo_suffix`, `freeTo_monotone_idempotent`). Concrete ring-buffer model (`InflightsConcrete`, `concreteAdd_abstract`, `ring_pos_ne`) added. See `FVSquad/Inflights.lean`. |
| 5 | `limit_size` utility | `src/util.rs` | 5 — Proofs | ✅ Done | All theorems proved (0 `sorry`). Budget helpers `limitSizeGo_count_add`, `limitSizeGo_budget'`, `limitSizeGo_stop_condition` enable proofs of `limitSize_sum_le` (budget safety) and `limitSize_maximal` (maximality). See `FVSquad/LimitSize.lean`. |
| 6 | `Progress` state machine | `src/tracker/progress.rs`, `src/tracker/state.rs` | 4 — Implementation | 🔄 In progress | Informal spec + Lean 4 spec + full implementation model (0 `sorry`). 25+ theorems proved covering `maybeUpdate`, `becomeProbe`, `becomeReplicate`, `becomeSnapshot`, `maybeDecrTo`. See `FVSquad/Progress.lean`. |

## Phase Legend

| Phase | Description |
|-------|-------------|
| 1 | Research — target identified, approach documented |
| 2 | Informal Spec — `specs/<name>_informal.md` written |
| 3 | Lean Spec — Lean 4 types + propositions (with `sorry`) |
| 4 | Implementation — Lean model of the Rust implementation |
| 5 | Proofs — `sorry`s removed, theorems fully proved |
