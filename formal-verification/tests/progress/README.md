# Progress State Machine Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Overview

Correspondence validation between the Lean 4 model `Progress`
(`formal-verification/lean/FVSquad/Progress.lean` / `ProgressCorrespondence.lean`)
and the Rust implementation `Progress` (`src/tracker/progress.rs`).

This is a Task 8 Route B validation: both sides are exercised on the same representative
inputs (three concrete fixtures × multiple operations), confirming that the functional
Lean model computes the same results as the Rust implementation.

## Lean model

- **File**: `formal-verification/lean/FVSquad/Progress.lean`
- **Correspondence file**: `formal-verification/lean/FVSquad/ProgressCorrespondence.lean`
- **Guard count**: 55 `#guard` compile-time assertions

## Rust tests

- **Function**: `tracker::progress::tests::test_progress_correspondence`
- **File**: `src/tracker/progress.rs`
- **Assertions**: 55 runtime `assert!` / `assert_eq!` checks

## Test fixtures

| Fixture | State | matched | next_idx | pending_snapshot |
|---------|-------|---------|----------|-----------------|
| `pReplicate` | Replicate | 5 | 6 | 0 |
| `pProbe` | Probe | 3 | 7 | 0 |
| `pSnapshot` | Snapshot | 2 | 3 | 10 |

## Test groups

| Group | Operations | Assertions |
|-------|-----------|------------|
| `maybeUpdate` | forward progress, no-op, next_idx advance, wf | 11 |
| `maybeDecrTo` Replicate | stale/non-stale, snapshot request | 8 |
| `maybeDecrTo` Probe | stale/non-stale, match_hint variants | 9 |
| `maybeDecrTo` Snapshot | stale/non-stale, snapshot request | 4 |
| `optimisticUpdate` | next_idx advance, field preservation, wf | 6 |
| State transitions | `becomeReplicate`, `becomeProbe` (×2), `becomeSnapshot` | 13 |
| `isPaused` | Probe paused/unpaused, Replicate (empty ins), Snapshot | 4 |
| **Total** | | **55** |

## Running

```bash
# Lean side (compile-time #guard assertions)
cd formal-verification/lean
lake build FVSquad.ProgressCorrespondence

# Rust side (runtime assertions)
cargo test test_progress_correspondence
# Or, as part of all correspondence tests:
cargo test correspondence --features protobuf-codec
```

## Results (as of 2026-04-26)

- Lean `#guard` tests: **55 pass** (verified at lake build time)
- Rust assertions: **55 pass** (cargo test)

## Correspondence level

**Abstraction** — the Lean model faithfully captures:
- All state transition functions (`becomeProbe`, `becomeReplicate`, `becomeSnapshot`)
- `maybeUpdate` matched/next_idx semantics
- `maybeDecrTo` stale detection and next_idx/pending_request_snapshot updates
- `optimisticUpdate` next_idx advance
- `isPaused` per-state logic

Known abstractions (not a divergence — intentional simplifications):
- **`Inflights` ring buffer**: Lean uses `ins_full : Bool`; Rust uses `Inflights.full()`.
  Correspondence is validated with a 256-capacity empty ring buffer (not full).
  Tests do not cover the `ins_full = true` Replicate path (would require adding inflights).
- **Overflow**: Lean uses `Nat` (no overflow); Rust uses `u64`. Not a practical concern.
- **`commit_group_id` / `committed_index`**: Not modelled in Lean; not tested here.
- **`recent_active`**: Modelled as a field but no theorems reason about it.
