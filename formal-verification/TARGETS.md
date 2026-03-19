# FV Targets — `raft-rs`

> 🔬 *Lean Squad — prioritised formal verification target list.*

| Priority | Target | File(s) | Phase | Status | Notes |
|----------|--------|---------|-------|--------|-------|
| 1 | `majority` + `MajorityConfig::vote_result` | `src/util.rs`, `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). See `FVSquad/MajorityQuorum.lean`. |
| 2 | `MajorityConfig::committed_index` | `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). Bridge lemma `countGe_eq_sorted_countP` completed the `committedIndex_safety` and `committedIndex_maximal` proofs. See `FVSquad/CommittedIndex.lean`. |
| 3 | `Unstable` log buffer | `src/log_unstable.rs` | 3 — Lean Spec | 🔄 In progress | Informal spec written (`specs/unstable_log_informal.md`). Lean spec written: types, invariants (indexCoherent, snapCoherent, wellFormed), all 6 methods modelled, case theorems for truncateAndAppend, invariant-preservation theorems. No `sorry`. See `FVSquad/UnstableLog.lean`. |
| 4 | `Inflights` ring buffer | `src/tracker/inflights.rs` | 1 — Research | ⬜ Not started | Circular buffer invariants |
| 5 | `limit_size` utility | `src/util.rs` | 4 — Implementation | 🔄 In progress | Lean spec + implementation model written: `FVSquad/LimitSize.lean`. Basic theorems proved (is_prefix, length_ge_one, singleton, empty, none, 6 decide examples). Budget/maximality theorems still `sorry`. |

## Phase Legend

| Phase | Description |
|-------|-------------|
| 1 | Research — target identified, approach documented |
| 2 | Informal Spec — `specs/<name>_informal.md` written |
| 3 | Lean Spec — Lean 4 types + propositions (with `sorry`) |
| 4 | Implementation — Lean model of the Rust implementation |
| 5 | Proofs — `sorry`s removed, theorems fully proved |
