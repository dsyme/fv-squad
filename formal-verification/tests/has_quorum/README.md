# Correspondence Test: `has_quorum`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Purpose

This directory contains the shared fixture for the **Route B correspondence test**
of `ProgressTracker::has_quorum` (`src/tracker.rs`).

The same 12 test cases are exercised on both sides:

| Side | File / Location | How to run |
|------|-----------------|------------|
| Lean | `FVSquad/HasQuorumCorrespondence.lean` | `lake build` (12 `#guard`) |
| Rust | `src/tracker.rs::test_has_quorum_correspondence` | `cargo test test_has_quorum_correspondence` |

## Correspondence level

**Exact** — the Lean `hasQuorum` function faithfully models the Rust
`ProgressTracker::has_quorum` algorithm:

- Rust `potential_quorum.get(&id).map(|_| true)` = Lean `if inSet v then some true else none`
- Rust `vote_result(check) == VoteResult::Won` = Lean `overlapCount voters inSet ≥ majority voters.length`
- Empty-voters convention: both return `true` / `Won`

## Fixture format (`cases.json`)

Each entry has:
- `id`: 1-based case number
- `voters`: list of voter IDs (`u64` / `Nat`)
- `set_ids`: IDs present in `potential_quorum`
- `expected`: `true` or `false`
- `note`: brief human explanation

## Test coverage (12 cases)

| Cases | Scenario |
|-------|---------|
| 1 | Empty voters (convention) |
| 2–3 | Single voter (present / absent) |
| 4–7 | 3-voter quorum (all outcome branches) |
| 8–12 | 5-voter quorum (boundary + non-consecutive IDs) |

## Commands

```bash
# Lean side
cd formal-verification/lean && lake build 2>&1 | grep -E "HasQuorumCorrespondence|error|#guard"

# Rust side
cargo test test_has_quorum_correspondence -- --nocapture
```
