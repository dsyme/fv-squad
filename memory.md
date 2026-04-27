# Lean Squad Memory — dsyme/raft-lean-squad

## Last Updated
Run 122 — 2026-04-27 15:30 UTC

## Repository
- **Language**: Rust (Raft consensus library)
- **FV Tool**: Lean 4 (v4.30.0-rc2, lakefile.toml, stdlib only — no Mathlib)
- **FV Directory**: `formal-verification/`
- **Lean Files**: 75 in `formal-verification/lean/FVSquad/`
- **Theorems**: ~681 (0 sorry)
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
UnstablePersistBridge, LeaderCompleteness (partial), ProgressTracker (PT1-PT26),
**progress_set (PS1-PS8, Run 122)** — ProgressSet.lean (8T, 0 sorry) + ProgressSetCorrespondence.lean (26 #guard)

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

## Active Gaps (from CRITIQUE.md Run 119)
1. **HLogConsistency full discharge**: connect AEBroadcastInvariant inductive closure to RaftReachable
2. **ProgressTracker integration**: all_wf in RaftReachable state (PT1-PT26 per-op but no RaftReachable connection)
3. **Term-indexed safety**: MC4 → RSS6/RSS8 (Raft §5.4.2)
4. **Paper/Report**: paper.tex updated Run 120 (673T/73F/20 layers) — PDF not compiled (LaTeX unavailable)
5. **progress_set**: Phase 5 ✅ — ProgressSet.lean (PS1–PS8, 0 sorry, Run 122) + ProgressSetCorrespondence.lean (26 #guard). PR submitted.

## Key Files
- `formal-verification/TARGETS.md` — prioritised target list
- `formal-verification/CORRESPONDENCE.md` — correspondence map (updated Run 118)
- `formal-verification/CRITIQUE.md` — proof utility critique (Run 119)
- `formal-verification/REPORT.md` — project report (Run 119, 673T/73F)
- `formal-verification/paper/paper.tex` — conference paper (Run 120, 673T/73F/20 layers)
- `formal-verification/specs/progress_set_informal.md` — informal spec (Run 120, PS1-PS8)

## Run 123 (2026-04-27) — Task 10 + Task 3

### Task 10: REPORT.md updated
- Status: 681T / 74F / 671 #guard
- Run 119-122 history appended

### Task 3: New target — MemStorageCore log operations
- **Informal spec**: `formal-verification/specs/mem_storage_informal.md` (MS1-MS8)
- **Lean spec**: `formal-verification/lean/FVSquad/MemStorage.lean`
- **Proved**: MS1 (compact advances firstIndex), MS2 (no-op), MS3 (suffix=ents), 
  MS4 (prefix preserved), MS5 (compact preserves contiguous), MS7 (lastIndex), MS8 (length)
- **Key lemma**: `firstIndex_after_drop` — dropping offset elts advances firstIndex by offset
- **Sorry**: MS6 (append preserves contiguous) — `firstIndex {take ++ ents}` equality is hard
  to prove via rw because `firstIndex` uses a `match` that Lean can't easily pattern-match
  against. Workaround needed: opaque function or different definition. Deferred to Task 5.
- **PR**: lean-squad/run-123-task10-task3-25004024142
- **Sorry count**: 1 (was 0 overall in prior files, now 1 in MemStorage.lean)

### Next steps
- Task 5: prove MS6 in MemStorage.lean (or restructure firstIndex definition to allow rw)
- Continue with other Phase 3 targets (LogUnstable, InflightProposal, etc.)
