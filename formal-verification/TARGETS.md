# FV Targets — `raft-rs`

> 🔬 *Lean Squad — prioritised formal verification target list.*

| Priority | Target | File(s) | Phase | Status | Notes |
|----------|--------|---------|-------|--------|-------|
| 1 | `majority` + `MajorityConfig::vote_result` | `src/util.rs`, `src/quorum/majority.rs` | 2 — Informal Spec | 🔄 In progress | Informal spec written; Lean spec next |
| 2 | `MajorityConfig::committed_index` | `src/quorum/majority.rs` | 1 — Research | ⬜ Not started | Core quorum commit algorithm |
| 3 | `Unstable` log buffer | `src/log_unstable.rs` | 1 — Research | ⬜ Not started | Index-offset rep invariant |
| 4 | `Inflights` ring buffer | `src/tracker/inflights.rs` | 1 — Research | ⬜ Not started | Circular buffer invariants |
| 5 | `limit_size` utility | `src/util.rs` | 1 — Research | ⬜ Not started | Good warmup; simple list truncation |

## Phase Legend

| Phase | Description |
|-------|-------------|
| 1 | Research — target identified, approach documented |
| 2 | Informal Spec — `specs/<name>_informal.md` written |
| 3 | Lean Spec — Lean 4 types + propositions (with `sorry`) |
| 4 | Implementation — Lean model of the Rust implementation |
| 5 | Proofs — `sorry`s removed, theorems fully proved |
