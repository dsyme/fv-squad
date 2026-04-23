# MaybePersistFUI Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

Runnable correspondence tests for `firstUpdateIndex` derivation and `maybePersistFui`.

## What Is Being Validated

The `first_update_index` computation in `src/raft_log.rs` (lines 560–565):

```rust
let first_update_index = match &self.unstable.snapshot {
    Some(s) => s.get_metadata().index,
    None => self.unstable.offset,
};
```

is modelled in Lean 4 as:

```lean
def firstUpdateIndex (snapshotIndex : Option Nat) (offset : Nat) : Nat :=
  snapshotIndex.getD offset
```

## Lean Model

- **File**: `formal-verification/lean/FVSquad/MaybePersistFUI.lean`
- **Theorems**: FU1–FU8 (8 theorems, 0 sorry)
- **Correspondence file**: `formal-verification/lean/FVSquad/MaybePersistFUICorrespondence.lean`
- **Guard count**: 20 `#guard` assertions

## Rust Tests

- **Function**: `test_maybe_persist_fui_correspondence`
- **File**: `src/raft_log.rs`
- **Cases**: 18 assertions across groups A, B, and C

## Test Groups

| Group | Description | Cases |
|-------|-------------|-------|
| A | `firstUpdateIndex` derivation (direct) | 4 |
| B | `maybePersistFui` no-snapshot path (FUI = offset = 7) | 8 |
| C | `maybePersistFui` snapshot path (FUI = snap.index = 3) | 6 |

## Running

```bash
# Lean side (compile-time guards)
cd formal-verification/lean && lake build FVSquad.MaybePersistFUICorrespondence

# Rust side
cargo test test_maybe_persist_fui_correspondence
```

## Results (as of 2026-04-23)

- Lean `#guard` tests: **20 pass** (verified at lake build time)
- Rust `assert_eq!` tests: **18 pass** (cargo test)

## Divergence Note

Group C tests demonstrate an important divergence between the Lean model and Rust:
the Lean model uses `logTerm : Nat → Nat` (total function, defaults to 0), while
Rust uses `store.term()` which can return `Err` when the entry is not in stable
storage. This means some cases where the Lean model would predict `true` (term
matches) actually return `false` in Rust (term lookup fails). This divergence is
documented in `formal-verification/CORRESPONDENCE.md` under the MaybePersist section.
