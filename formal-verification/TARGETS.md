# FV Targets — `raft-rs`

> 🔬 *Lean Squad — prioritised formal verification target list.*

| Priority | Target | File(s) | Phase | Status | Notes |
|----------|--------|---------|-------|--------|-------|
| 1 | `majority` + `MajorityConfig::vote_result` | `src/util.rs`, `src/quorum/majority.rs` | 5 — Proofs | ✅ Done | All theorems proved (no `sorry`). See `FVSquad/MajorityQuorum.lean`. |
| 2 | `MajorityConfig::committed_index` | `src/quorum/majority.rs` | 4 — Implementation | 🔄 In progress | Lean spec + impl model written. Monotonicity fully proved. Safety/maximality proofs structured with sub-lemmas: `hstep_A` (countP lower bound) and `hstep_B` (countP upper bound) proved; remaining sorry is the `Finset.card_filter → List.countP` bridge. |
| 3 | `Unstable` log buffer | `src/log_unstable.rs` | 1 — Research | ⬜ Not started | Index-offset rep invariant |
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
