# ProgressTracker Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Overview

Correspondence tests for `ProgressTracker::apply_conf` (source: `src/tracker.rs`)
against the Lean model in `formal-verification/lean/FVSquad/ProgressTrackerCorrespondence.lean`.

## Lean side

File: `formal-verification/lean/FVSquad/ProgressTrackerCorrespondence.lean`

33 `#guard` tests covering:
- `removePeer` (Lean guards 1–5): size reduction, absence of removed peer, others preserved
- `insertPeer` (Lean guards 6–10): count increase, fresh peer properties, no duplication on re-add
- `updatePeer` (Lean guards 11–13): function applied to target, others unchanged, absent id safe
- `applyChange` Add/Remove (Lean guards 14–19): semantics for single changes
- `applyChanges` sequences (Lean guards 20–23): empty, Add-then-Remove, Remove-then-Add, two adds
- `initTracker` (Lean guards 24–27): length, next_idx values, matched=0
- `all_wf` invariant checks (Lean guards 28–33): wf preserved after all operations

## Rust side

Test function: `tracker::tests::test_progress_tracker_correspondence` in `src/tracker.rs`

Covers 15 cases mapping to the Lean `#guard` tests above:
- `removePeer` (5 cases)
- `insertPeer/Add` (3 cases)
- `applyChanges` sequences (4 cases)
- `all_wf` invariant (1 case)

## Running

```bash
# Lean side (compile-time #guard)
cd formal-verification/lean && lake build FVSquad.ProgressTrackerCorrespondence

# Rust side
cargo test test_progress_tracker_correspondence
```

## Correspondence level

**Abstraction**: The Lean model uses an association list (allowing duplicate keys);
the Rust uses a `HashMap` (unique keys).  The observable properties tested —
size changes, peer presence/absence, per-peer field values, wf invariant — are
semantically equivalent between the two representations.

## Last updated

Run 97 (2026-04-24). 33 Lean `#guard` tests + 15 Rust assertions, all passing.
