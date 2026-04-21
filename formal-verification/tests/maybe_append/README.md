# Correspondence Tests: `maybe_append`

This directory contains test fixtures validating correspondence between the Lean 4 model
`maybeAppend` (in `FVSquad/MaybeAppendCorrespondence.lean`) and the Rust implementation
`RaftLog::maybe_append` (in `src/raft_log.rs`).

## Purpose

Task 8 (Route B) of the Lean Squad workflow verifies that the abstract Lean model and the
concrete Rust implementation agree on observable input/output behaviour for a selected set
of representative cases.  Agreement is checked at two levels:

| Level | Where checked | Tool |
|-------|--------------|------|
| Lean model | `FVSquad/MaybeAppendCorrespondence.lean` | `#guard` (compile-time) |
| Rust implementation | `src/raft_log.rs` `test_maybe_append_correspondence` | `cargo test` |

Both test suites use exactly the same 8 cases defined in `cases.json`.

## Running the tests

```bash
# Lean – compile-time guards (run from repo root)
cd formal-verification/lean
lake build FVSquad.MaybeAppendCorrespondence

# Rust – unit test
cargo test test_maybe_append_correspondence
```

## Case summary

| ID | Description | prev_idx | prev_term | entries | expected conflict |
|----|-------------|----------|-----------|---------|------------------|
| 1 | Non-match: wrong prevTerm | 1 | 5 | [] | None |
| 2 | Match, empty entries, commit=0 | 3 | 3 | [] | 0 |
| 3 | Match, empty entries, commit=2 | 3 | 3 | [] | 0 |
| 4 | All entries match | 1 | 1 | [(2,2),(3,3)] | 0 |
| 5 | New entries beyond log | 3 | 3 | [(4,4),(5,5)] | 4 |
| 6 | Partial match then conflict | 1 | 1 | [(2,2),(3,5)] | 3 |
| 7 | Singleton log, extend by 1 | 1 | 1 | [(2,2)] | 2 |
| 8 | Conflict at last entry | 2 | 2 | [(3,5)] | 3 |

## Correspondence model

The Lean model `maybeAppend` is a pure-functional abstraction of the Rust `maybe_append`
method.  It omits:

- Protobuf serialisation / deserialisation
- Disk persistence and I/O side effects
- Panic / error-path behaviour (modelled as `none` return)
- `RaftLog` struct fields unrelated to log entries (`unstable`, `committed`, `applied`)

See `formal-verification/CORRESPONDENCE.md` for a detailed per-function correspondence table.
