# MaybeCommit Correspondence Tests

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Overview

This directory contains correspondence-test fixtures for `RaftLog::maybe_commit` and
`RaftLog::commit_to` (`src/raft_log.rs`).

The Lean model under test is in
`formal-verification/lean/FVSquad/MaybeCommitCorrespondence.lean`.

## Fixture

**Log**: entries at indices 1–5 with terms 1, 1, 2, 2, 3 respectively, stabilised
in storage via `MemStorage`. Initial `committed = 0`.

```
  index:   0   1   2   3   4   5   6+
  term:    —   1   1   2   2   3   none
  committed = 0
```

## Cases (`cases.json`)

| ID  | committed_start | max_index | term | expected_result | expected_committed | Note |
|-----|-----------------|-----------|------|-----------------|--------------------|------|
|  1  | 0               | 3         | 2    | true            | 3                  | advance: log[3]=2, term=2 |
|  2  | 3               | 3         | 2    | false           | 3                  | no advance: maxIndex = committed |
|  3  | 4               | 3         | 2    | false           | 4                  | no advance: maxIndex < committed |
|  4  | 0               | 3         | 1    | false           | 0                  | term mismatch: log[3]=2, want 1 |
|  5  | 0               | 6         | 1    | false           | 0                  | no entry at index 6 |
|  6  | 2               | 3         | 2    | true            | 3                  | single-step advance |
|  7  | 1               | 5         | 3    | true            | 5                  | advance to last entry |
|  8  | 0               | 1         | 1    | true            | 1                  | advance to first entry |
|  9  | 0               | 1         | 2    | false           | 0                  | wrong term at 1 (log[1]=1) |
| 10  | 0               | 4         | 2    | true            | 4                  | advance to index 4 (log[4]=2) |

Plus 4 `commit_to` cases (IDs 11–14) testing monotonicity and no-op behaviour.

## Running

**Lean side** (compile-time `#guard` assertions):
```bash
cd formal-verification/lean
lake build FVSquad.MaybeCommitCorrespondence
```

**Rust side** (runtime assertions):
```bash
cargo test test_maybe_commit_correspondence --features protobuf-codec
```

## Correspondence level

**Abstraction** — the Lean model captures the pure input-to-output mapping of
`maybe_commit` and `commit_to`, abstracting away:
- Logging (`debug!` calls)
- The `fatal!` panic branch in `commit_to` when `to_commit > last_index`
  (modelled as a call-site precondition; all test cases satisfy it)

## Files

- `cases.json` — 10 `maybe_commit` test cases in machine-readable form
- `README.md` — this file
