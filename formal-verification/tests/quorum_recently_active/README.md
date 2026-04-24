# quorum_recently_active — Correspondence Tests

## Target

`ProgressTracker::quorum_recently_active` in `src/tracker.rs` (lines 336–352).

## Lean model

`FVSquad.QuorumRecentlyActive.quorumRecentlyActive`  
defined in `formal-verification/lean/FVSquad/QuorumRecentlyActive.lean`.

## Correspondence level

**Abstraction** — the Lean model faithfully captures the active-voter logic; the
only abstraction is that `Progress.ins` (a ring-buffer) is modelled as a boolean
`ins_full` (see `ProgressCorrespondence.lean`), which does not affect the
`recent_active` field used here.

## Test cases (`cases.json`)

14 cases covering:

| # | Scenario |
|---|----------|
| 1 | empty voters → vacuous quorum |
| 2–3 | single voter, leader present / absent |
| 4–8 | three voters, varying active counts around the majority boundary |
| 9–11 | five voters, majority = 3, boundary cases |
| 12–14 | perspectiveOf ≠ 1; leader-identity varies |

Each entry records: `voters`, `entries` (node id + `recent_active` flag),
`perspective_of`, and the `expected` boolean result.

## Rust test

`tracker::tests::test_quorum_recently_active_correspondence` in `src/tracker.rs`.
Run with:

```
cargo test test_quorum_recently_active_correspondence
```

## Lean `#guard` tests

`formal-verification/lean/FVSquad/QuorumRecentlyActiveCorrespondence.lean`  
(14 `#guard` assertions, verified at compile time by `lake build`).
