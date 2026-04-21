# log_unstable Correspondence Tests

> 🔬 *Lean Squad — Task 8 Route B correspondence tests.*

## What is validated

`Unstable` query operations from `src/log_unstable.rs`. The Lean model in
`FVSquad/LogUnstable.lean` abstracts full `Entry` objects as just their terms
(a `List Nat`), since the index is implicit from `offset`.

## Abstraction

| Lean | Rust |
|------|------|
| `entries : List Nat` (terms) | `entries : Vec<Entry>` (index + term + data) |
| `entries[i]` = term of entry at index `offset + i` | `entries[i].term`; `entries[i].index = offset + i` |
| `snapshot = some (idx, term)` | `snapshot = Some(Snapshot { metadata: {index, term} })` |
| `maybeFirstIndex u` | `u.maybe_first_index()` |
| `maybeLastIndex u` | `u.maybe_last_index()` |
| `maybeTerm u idx` | `u.maybe_term(idx)` |

## Test commands

**Lean (static, at build time):**
```bash
cd formal-verification/lean
lake build FVSquad.LogUnstableCorrespondence
```

**Rust (runtime):**
```bash
cargo test test_log_unstable_correspondence
```

## Cases (12 total)

| ID | State | Query | Expected |
|----|-------|-------|---------|
| 1  | entries=[10,20,30] offset=5 snap=none | maybeFirstIndex | none |
| 2  | entries=[] offset=5 snap=(4,9) | maybeFirstIndex | some 5 |
| 3  | entries=[10,20,30] offset=5 | maybeLastIndex | some 7 |
| 4  | entries=[] snap=none | maybeLastIndex | none |
| 5  | entries=[] snap=(4,9) | maybeLastIndex | some 4 |
| 6  | entries=[10,20,30] offset=5 | maybeTerm(5) | some 10 |
| 7  | entries=[10,20,30] offset=5 | maybeTerm(6) | some 20 |
| 8  | entries=[10,20,30] offset=5 | maybeTerm(7) | some 30 |
| 9  | entries=[10,20,30] offset=5 | maybeTerm(8) | none (beyond) |
| 10 | entries=[10,20,30] offset=5 snap=none | maybeTerm(4) | none (before) |
| 11 | entries=[] snap=(4,9) | maybeTerm(4) | some 9 |
| 12 | entries=[] snap=(4,9) | maybeTerm(3) | none (before snap) |

## Result

Both sides agree on all 12 cases. Correspondence level: **Exact** for the
data-only paths tested. Data payload is abstracted away (only index/term matter).
