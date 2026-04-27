# Lean Squad Memory — dsyme/raft-lean-squad

## Last Updated
Run 125 — 2026-04-27 17:40 UTC (composition assessment: A3-A6 phases corrected, A7 chartered)

## Repository
- **Language**: Rust (Raft consensus library)
- **FV Tool**: Lean 4 (v4.30.0-rc2, lakefile.toml, stdlib only — no Mathlib)
- **FV Directory**: `formal-verification/`
- **Lean Files**: 75 in `formal-verification/lean/FVSquad/`
- **Theorems**: ~689 (0 sorry)
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

## Active Gaps (from Run 125 composition assessment)
1. **A7 (election_lifecycle_bridge)** — THE SINGLE REMAINING GAP FOR FULL COMPOSITION:
   Create `FVSquad/ElectionLifecycle.lean` with:
   - `ElectionEpoch` structure: winner, term, voters, broadcast round
   - Show elected leader's AE broadcast satisfies `BroadcastSeq` / `ValidAEStep` preconditions
   - Apply EBC6 (broadcastSeq_hqc_preserved) + CPS13 → unconditional `hqc_preserved`
   - Connect to `RaftReachable.step` → unconditional `raftReachable_safe`
   - Also integrate MC4 (term-safety) into the election lifecycle
   - Estimated: ~20–40 theorems, difficulty medium-high
2. **ProgressTracker integration**: PT1-PT26 per-op but no RaftReachable connection
3. **Paper/Report**: paper.tex updated Run 120 (673T/73F/20 layers) — PDF not compiled (LaTeX unavailable)

## Composition Status (Run 125)
All 5 `RaftReachable.step` hypotheses status:
- `hlogs'`: ✅ Discharged (CPS8/CPS9 + ValidAEStep model)  
- `hno_overwrite`: ✅ Discharged (CPS1)
- `hcommitted_mono`: ✅ Discharged (CPS11)
- `hnew_cert`: ✅ Discharged (CR8 + MC4)
- `hqc_preserved`: ⚠️ Conditionally discharged (EBC6 + ECM6 + CPS13 chain — needs A7 bridge)

Proof chain for `hqc_preserved`: RE5/RE7 → [A7 gap] → EBC6 → ECM6 → CPS13 → RaftReachable.step ✅

A3-A6 phases updated in TARGETS.md (were stale at Phase 1, now correctly Phase 5 ✅)

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


### Run 124 (2026-04-27) — Task 4 + Task 5

### Task 4: Implementation Extraction — MemStorageCore
- **Model**: `MemStorageCore` structure with `snapshotIndex : Nat` + `terms : List Nat`
  (contiguity baked in: entry i has log index `snapshotIndex + 1 + i`)
- **Definitions**: `firstIndex`, `lastIndex`, `compact`, `append`
- **Source**: `src/storage.rs` (`MemStorageCore::compact`, `append`, `first_index`, `last_index`)
- **Lean file**: `FVSquad/MemStorage.lean`

### Task 5: Proof Assistance — MS1-MS8 all proved
- **MS1**: `firstIndex ≤ lastIndex + 1`
- **MS2**: `terms = [] ↔ lastIndex < firstIndex`
- **MS3**: `compact` no-op when `ci ≤ firstIndex`
- **MS4**: `compact` preserves `lastIndex`
- **MS5**: `firstIndex (compact s ci) = max (firstIndex s) ci`
- **MS6**: `append` preserves `firstIndex`
- **MS7**: `lastIndex = startIndex + length - 1` (non-empty append)
- **MS8**: `append [] = no-op`
- **Sorry count**: 0. `lake build` passed (77 jobs, Lean 4.30.0-rc2)
- **PR**: lean-squad/run-124-memstorage-task4-task5-25006260511

### Next steps
- Task 5: prove MS6 in MemStorage.lean (or restructure firstIndex definition to allow rw)
- Continue with other Phase 3 targets (LogUnstable, InflightProposal, etc.)
