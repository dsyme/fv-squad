# Correspondence Test: `vote_result`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Purpose

This directory contains the shared fixture for the **Route B correspondence test**
of `Configuration::vote_result` (`src/quorum/majority.rs`).

The same 12 test cases are exercised on both sides:

| Side | File / Location | How to run |
|------|-----------------|------------|
| Lean | `FVSquad/VoteResultCorrespondence.lean` | `lake build` (12 `#guard`) |
| Rust | `src/quorum/majority.rs::test_vote_result_correspondence` | `cargo test test_vote_result_correspondence` |

## Correspondence level

**Exact** — the Lean `voteResult` function faithfully models the Rust
`Configuration::vote_result` algorithm:

- Rust empty-voters convention (`return VoteResult::Won`) = Lean `match voters with | [] => VoteResult.Won`
- Rust yes/missing counts from the `check` closure = Lean `yesCount` / `missingCount` recursion
- Rust majority threshold `crate::majority(n)` = Lean `majority n = n / 2 + 1`
- Three-way outcome (Won/Pending/Lost) = Lean `VoteResult` inductive type

## Fixture format (`cases.json`)

Each entry has:
- `id`: 1-based case number
- `voters`: list of voter IDs (`u64` / `Nat`)
- `yes_ids`: voters that voted yes (`Some(true)`)
- `no_ids`: voters that voted no (`Some(false)`)
- IDs not in `yes_ids` or `no_ids` are **missing** (`None`)
- `expected`: one of `"Won"`, `"Pending"`, `"Lost"`
- `note`: brief human explanation

## Test coverage (12 cases)

| Cases | Scenario |
|-------|---------|
| 1 | Empty voters (convention) |
| 2–4 | Single voter (yes / no / missing) |
| 5–9 | 3-voter quorum (all outcome branches) |
| 10–12 | 5-voter quorum (boundary at majority threshold) |

## Commands

```bash
# Lean side
cd formal-verification/lean && lake build 2>&1 | grep -E "VoteResultCorrespondence|error|#guard"

# Rust side
cargo test test_vote_result_correspondence -- --nocapture
```
