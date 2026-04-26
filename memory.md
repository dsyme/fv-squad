# Lean Squad Memory — dsyme/raft-lean-squad

## Last Updated
Run 118 — 2026-04-26 09:30 UTC

## Repository
- **Language**: Rust (Raft consensus library)
- **FV Tool**: Lean 4 (v4.30.0-rc2, lakefile.toml, stdlib only — no Mathlib)
- **FV Directory**: `formal-verification/`
- **Lean Files**: 73 in `formal-verification/lean/FVSquad/`
- **Theorems**: ~722 (0 sorry)
- **CI**: `.github/workflows/lean-ci.yml` — threshold 25 Rust correspondence tests

## Status Issue
- Issue #139 — `[Lean Squad] Formal Verification Status` (open)

## Completed Targets (Phase 5, all proved, 0 sorry)
limit_size, config_validate, vote_result, committed_index, find_conflict, find_conflict_by_term,
maybe_append, joint_vote_result, joint_committed_index, inflights, progress, is_up_to_date,
log_unstable, tally_votes, has_quorum, quorum_recently_active, safety_composition, joint_tally,
joint_safety_composition, raft_protocol, raft_trace, progress_tracker, configuration_invariants,
multistep_reachability, election_model (RaftElection.lean), AEBroadcastInvariant, BroadcastLifecycle,
ElectionBroadcastChain, ConcreteProtocolStep, ElectionConcreteModel, CommitRule, HasNextEntries,
NextEntries, MaybeCommit, MaybePersist, MaybePersistFUI, RaftLogAppend, ReadOnly, UncommittedState,
UnstablePersistBridge, LeaderCompleteness (partial), ProgressTracker (PT1-PT26)

## Correspondence Tests (25 Rust test functions)
All in `formal-verification/tests/` with Lean `#guard` counterparts.
- ProgressTrackerCorrespondence: 47 #guard (PT25/PT26 added Run 116)
- See state.json for full target list

## CI Status (Run 118 audit)
- `lean-ci.yml`: healthy. Threshold updated 20→25 (Run 118).
- lean-toolchain: v4.30.0-rc2 ✅
- Correspondence test job: `cargo test correspondence --features protobuf-codec`

## Pending/Conflicts
- `proofs-r130` branch (RaftSafety.lean + CRITIQUE.md changes): CONFLICT with main — skip for reconciliation run
- run-117 branch not found remotely (may not have been pushed); changes recorded in state.json tentatively

## Active Gaps (from CRITIQUE.md Run 112)
1. **LeaderCompleteness full chain**: `HLogConsistency` still hypothetical; highest priority
2. **Term-indexed safety**: connecting MaybeCommit MC4 to top-level proof
3. **ProgressTracker integration**: PT1-PT26 per-op but no RaftReachable connection
4. **Paper/Report**: last updated Run 115 (671T) — needs update for Runs 116-118

## Key Files
- `formal-verification/TARGETS.md` — prioritised target list
- `formal-verification/CORRESPONDENCE.md` — correspondence map (updated Run 118)
- `formal-verification/CRITIQUE.md` — proof utility critique (Run 112)
- `formal-verification/REPORT.md` — project report (Run 115)
- `formal-verification/paper/paper.tex` — conference paper (Run 108)

## Notes
- PR workflow: all Lean Squad PRs labeled `lean-squad`; merge open PRs at start of each run
- Status issue #139 updated each run with run history entry
