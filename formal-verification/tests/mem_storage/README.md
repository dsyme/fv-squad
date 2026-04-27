# mem_storage Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Overview

This directory contains **Task 8 Route B** correspondence validation for
`MemStorageCore` log operations (`src/storage.rs`) against the Lean 4 formal model
`FVSquad.MemStorage` (`formal-verification/lean/FVSquad/MemStorage.lean`).

**Approach**: Both sides are evaluated on the same 16 fixture cases from `cases.json`.

- **Lean side**: `#guard` assertions in `MemStorageCorrespondence.lean` run the Lean model at
  `lake build` time (compile-time evaluation).
- **Rust side**: `test_mem_storage_correspondence` in `src/storage.rs` runs the same
  cases at `cargo test` time.

If both pass, the Lean model and the Rust implementation produce identical results on all
16 cases.

## Directory Contents

| File | Purpose |
|------|---------|
| `cases.json` | Shared fixture: 16 test cases covering `firstIndex`, `lastIndex`, `compact`, `append` |
| `README.md` | This file |

The test code lives in:
- `formal-verification/lean/FVSquad/MemStorageCorrespondence.lean` — Lean side (`#guard`)
- `src/storage.rs::test_mem_storage_correspondence` — Rust side (`assert_eq!`)

## Operations Tested

| Operation | Cases | Properties exercised |
|-----------|-------|---------------------|
| `firstIndex` | 3 | empty log, non-empty log, snapshot offset |
| `lastIndex` | 3 | empty log, non-empty log, snapshot offset |
| `compact` | 4 | noop (ci = fi), drop 1, ci < fi (noop), compact all entries |
| `append` | 6 | replace-all, replace-last, extend, truncate, empty noop, insert mid |

## Correspondence Level

**Abstraction**: The Lean model tracks only entry terms (not payloads, conf states,
hard state, or error paths). The Rust implementation operates on `Entry` values
(protobuf structs with index+term+data). Both sides agree on the term list and log
index range for all 16 fixture cases.
