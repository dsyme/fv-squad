# RaftLog::append Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Overview

This directory documents the correspondence validation for `RaftLog::append`
(`src/raft_log.rs:382`) against the Lean model `raftLogAppend`
(`formal-verification/lean/FVSquad/RaftLogAppendCorrespondence.lean`).

## Fixtures

### Base log
- Stable storage: entries at indices 1→term1, 2→term2 (`stableLastIdx = 2`)
- Unstable segment: empty at `offset = 3`
- `committed = 0`

### Extended log
- Same stable storage as base
- Unstable segment: entries `[2, 3]` at `offset = 3` (index 3→term2, index 4→term3)

## Test Cases (21 correspondence points)

| ID | Fixture | Input batch       | Expected lastIdx | Expected offset | Expected unstable entries | Branch |
|----|---------|-------------------|-----------------|-----------------|---------------------------|--------|
| 1  | base    | []                | 2               | 3               | []                        | empty  |
| 2  | base    | [(3,2)]           | 3               | 3               | [2]                       | append |
| 3  | base    | [(1,2)]           | 1               | 1               | [2]                       | replace|
| 4  | base    | [(2,3),(3,3)]     | 3               | 2               | [3,3]                     | replace|
| 5  | ext     | []                | 4               | 3               | [2,3]                     | empty  |
| 6  | ext     | [(5,4)]           | 5               | 3               | [2,3,4]                   | append |
| 7  | ext     | [(4,4)]           | 4               | 3               | [2,4]                     | trunc  |
| 8  | base    | [(3,2)]           | committed = 0 (unchanged)                                  | inv    |
| 9  | ext     | [(4,4)]           | committed = 0 (unchanged)                                  | inv    |
|10  | base    | [(3,2)]           | stable storage last_index = 2 (unchanged)                  | inv    |
|11  | ext     | [(5,4)]           | stable storage last_index = 2 (unchanged)                  | inv    |

(Cases 8–11 are cross-check invariants mirroring theorems RA4 and RA5 in `RaftLogAppend.lean`.)

## Running the Tests

**Lean side** (compile-time `#guard` assertions — verified by `lake build`):
```bash
cd formal-verification/lean
lake build FVSquad.RaftLogAppendCorrespondence
```

**Rust side** (runtime `assert_eq!` assertions):
```bash
cargo test test_raft_log_append_correspondence
```

## Correspondence Level

**Abstraction**: the Lean model faithfully captures the three structural branches of
`truncate_and_append` but abstracts away:
- Entry payloads (only index+term modelled)
- `entries_size` byte accounting
- The logger/tracing side effects
- The `after < committed` panic path (success path only)

The `raftLastIndex` return value and the `unstable.{offset, entries}` state after
each `append` call are verified to match exactly.
