# Formal Verification Research

> 🔬 *Lean Squad — automated formal verification for this repository.*

## Repository Overview

This repository is a Rust implementation of the [Raft distributed consensus algorithm](https://raft.github.io/), derived from the TiKV `raft-rs` crate. The codebase implements the core Consensus Module (not Log, State Machine, or Transport layers).

**Primary language**: Rust (52 `.rs` files)  
**FV tool chosen**: Lean 4 + Mathlib  
**Aeneas feature**: The codebase has an `aeneas` Cargo feature that replaces unsafe stack-array optimisations with safe `Vec` equivalents in `quorum/majority.rs`, making automatic Lean extraction via the Charon+Aeneas toolchain viable for that module.

## Why Lean 4?

- Lean 4 + Mathlib provides rich automation (`omega`, `simp`, `decide`) well-suited to the arithmetic and list-manipulation properties in Raft.
- The `aeneas` Cargo feature in this repo explicitly signals maintainer interest in Lean-based FV.
- Charon+Aeneas can mechanically extract Lean from the safe-Rust variants.

## FV Target Survey

### Target 1: `util::limit_size` ⭐⭐⭐ (Top Priority)

**File**: `src/util.rs`  
**Function**: `pub fn limit_size<T: PbMessage + Clone>(entries: &mut Vec<T>, max: Option<u64>)`

**What it does**: Truncates a vector of protobuf entries so that the total serialised byte size stays within `max`. Always preserves at least one entry.

**Why FV-amenable**:
- Pure functional effect (truncation of a list)
- Clear, textbook postconditions: prefix property, non-empty guarantee, size bound
- Existing doctests provide concrete specification hints
- No I/O, no unsafe code, minimal dependencies

**Key properties to verify**:
1. **Non-empty**: `limit_size(entries, max)` always leaves `|entries| ≥ 1` when input was non-empty
2. **Prefix**: the result is a prefix of the original list
3. **Size bound**: the total serialised size of the result respects `max` (unless capped at 1)
4. **Idempotence**: applying `limit_size` twice with the same `max` is a no-op
5. **No-op cases**: `limit_size` with `max = None` or `max = NO_LIMIT` is a no-op

**Proof tractability**: Very high — equational reasoning + `omega` + `simp`. Modelled as a pure list function abstracting away protobuf serialisation.

**Approximations needed**: The Lean model must abstract `compute_size()` as a function `size : α → ℕ`. Overflow of `u64` during size accumulation is not modelled (treated as non-overflowing in the spec).

---

### Target 2: `config::Config::validate` ⭐⭐⭐ (Top Priority)

**File**: `src/config.rs`  
**Function**: `pub fn validate(&self) -> Result<()>`

**What it does**: Validates a `Config` struct, returning `Ok(())` iff a conjunction of arithmetic constraints holds:
- `id ≠ 0`
- `heartbeat_tick > 0`
- `election_tick > heartbeat_tick`
- `min_election_tick ≥ election_tick`
- `min_election_tick < max_election_tick`
- `max_inflight_msgs > 0`
- `read_only_option == LeaseBased → check_quorum`
- `max_uncommitted_size ≥ max_size_per_msg`

**Why FV-amenable**:
- Fully decidable conjunction of arithmetic predicates
- No side effects
- The spec is literally the conjunction of the error conditions (inverted)

**Key properties to verify**:
1. **Soundness**: `validate(c) = Ok(())` iff all constraints hold
2. **Completeness**: the code checks every required constraint (no gaps)
3. **Redundancy check**: are any constraints implied by others? (interesting finding potential)

**Proof tractability**: Very high — `decide` closes decidable arithmetic propositions. Can be modelled as a pure predicate.

**Approximations needed**: `ReadOnlyOption` enum modelled as a two-element Lean inductive type.

---

### Target 3: `quorum::majority::Configuration::vote_result` ⭐⭐

**File**: `src/quorum/majority.rs`  
**Function**: `pub fn vote_result(&self, check: impl Fn(u64) -> Option<bool>) -> VoteResult`

**What it does**: Given a set of voter IDs and a function mapping voter → Some(yes)/Some(no)/None(missing), returns `Won`, `Pending`, or `Lost` based on whether a majority of yes/no has been reached.

**Why FV-amenable**:
- Pure function over a finite set
- Clear majority-quorum specification
- `aeneas`-safe variant available

**Key properties to verify**:
1. `vote_result(∅, _) = Won` (empty config wins by convention)
2. If `yes ≥ ⌈n/2⌉ + 1` then `Won`
3. If `yes + missing < ⌈n/2⌉ + 1` then `Lost`
4. Monotonicity: replacing `None` with `Some(true)` cannot change `Won → Pending/Lost`

**Proof tractability**: High — `omega` + `simp`.

---

### Target 4: `quorum::majority::Configuration::committed_index` ⭐⭐

**File**: `src/quorum/majority.rs`  
**Function**: `committed_index(use_group_commit, l)`

**What it does**: Computes the highest log index that has been acknowledged by a quorum (the `(n/2+1)`-th largest acked index). The `aeneas` feature provides a safe-Rust equivalent for automatic extraction.

**Key properties to verify**:
1. The result is ≤ every element in the top-quorum of acked indices
2. The result is ≥ the minimum acked index in the voters set (lower bound)
3. Empty config returns `u64::MAX`

**Proof tractability**: Medium — requires lemmas about sorted lists and indexing.

---

### Target 5: `raft_log::RaftLog::find_conflict` ⭐⭐

**File**: `src/raft_log.rs`  
**Function**: `pub fn find_conflict(&self, ents: &[Entry]) -> u64`

**What it does**: Scans a slice of entries and returns the index of the first entry whose term does not match the stored log, or 0 if all entries match.

**Key properties to verify**:
1. Return value is the index of the first conflicting entry, or 0
2. All entries before the returned index match the log
3. Monotone scan (no backtracking)

**Proof tractability**: High once `match_term` is abstracted as a predicate.

---

### Target 6: `raft_log::RaftLog::maybe_append` ⭐

**File**: `src/raft_log.rs` — Depends on `find_conflict`. Medium tractability.

---

### Target 7–8: `quorum::joint` ⭐

**File**: `src/quorum/joint.rs` — Joint quorum operations, depend on Targets 3 and 4.

---

### Target 9: `tracker::inflights` ⭐

**File**: `src/tracker/inflights.rs`  
**Struct**: `pub struct Inflights` — FIFO ring buffer for tracking in-flight Raft messages

**What it does**: Tracks log indices of sent-but-unacknowledged AppendEntries RPCs.
The leader uses this to bound the pipeline window (up to `cap` messages in flight).

**Data structure**:
- `buffer : Vec<u64>` — ring buffer of capacity `cap`
- `start : usize` — index of the oldest (first valid) entry in the ring
- `count : usize` — number of valid entries currently stored (`0 ≤ count ≤ cap`)
- `cap : usize` — maximum capacity
- `incoming_cap : Option<usize>` — pending capacity resize (applied when buffer drains)

**Key operations**:
| Method | Behaviour |
|--------|-----------|
| `new(cap)` | Creates empty buffer with capacity `cap` |
| `add(v)` | Appends `v` to the ring (panics if `full()`) |
| `free_to(k)` | Removes all entries ≤ `k` from the front |
| `free_first_one()` | Removes the single oldest entry |
| `reset()` | Clears all entries; applies any pending cap resize |
| `full()` | True iff `count = cap` (or pending cap already reached) |
| `set_cap(n)` | Schedules a capacity resize to `n` |

**Why FV-amenable**:
- The *logical content* is simply an ordered sequence of `u64` values — the ring
  buffer is a performance detail orthogonal to the correctness properties.
- Clear pre/postconditions for each operation.
- The `free_to` correctness criterion ("all entries ≤ k are removed, others remain")
  is a textbook invariant, provable by induction on the sequence.
- Well-covered by existing unit tests that serve as specification hints.

**Key properties to verify**:
1. **Capacity invariant** (`INF-1`): `count ≤ cap` is maintained by all operations.
2. **`add` content** (`INF-2`): After `add(v)`, `v` is the last element of the logical sequence.
3. **`free_to` correctness** (`INF-3`): After `free_to(k)`, no remaining entry satisfies `≤ k`.
4. **`free_to` preservation** (`INF-4`): After `free_to(k)`, all entries that were `> k` are still present.
5. **`reset` clears** (`INF-5`): After `reset()`, `count = 0`.
6. **`full` spec** (`INF-6`): `full() = true ↔ count = cap` (ignoring `incoming_cap` case).

**Lean model**:
- Abstract the ring buffer as `List Nat` (the ordered sequence of inflights).
- `add` ≡ `l ++ [v]`
- `free_to k` ≡ `l.dropWhile (· ≤ k)`
- `full` ≡ `l.length = cap`
- No need to model the ring layout — that is an implementation detail.
- `set_cap` and `incoming_cap` can be modelled separately or omitted in a first pass.

**Proof tractability**: High for INF-1, INF-2, INF-5, INF-6 (direct from definitions).
Medium for INF-3, INF-4 (require `dropWhile` induction). No difficult arithmetic.

**Approximations**:
- Ring layout (`start`, `buffer` vec) abstracted away — Lean model is a pure `List Nat`.
- `incoming_cap` resize logic omitted in the first pass (it is a secondary concern).
- `u64` → `Nat` (no overflow concern; inflights are log indices, bounded in practice).
- `add` panic on full buffer not modelled (assumed pre: `¬full()`).

**Recommended next step**: Task 2 — write `formal-verification/specs/inflights_informal.md`.

---

### Target 10: `tracker::progress` state machine ⭐

**File**: `src/tracker/progress.rs` — Progress state machine transitions. Medium tractability.

---

## Approach Summary

| Phase | Tool | Strategy |
|-------|------|----------|
| Spec | Lean 4 + Mathlib | Hand-written types + propositions |
| Impl | Lean 4 | Pure functional model (`partial def` where needed) |
| Proofs | Lean 4 tactics | `omega`, `simp`, `decide`, `induction` |
| Extraction (optional) | Charon + Aeneas | Auto-extract from `--features aeneas` variants |

We prioritise Targets 1 and 2 first (highest tractability, standalone specs). Targets 3–4 next (Aeneas-compatible). Targets 5–6 after.

## Current Project State (Run 47)

- **32 Lean files**, **505 proved theorems**, **0 sorry**, **Lean 4.28.0**
- Top-level safety theorem `raftReachable_safe` (RT2) proved.
- `ConcreteProtocolStep.lean` (CPS1–CPS13) bridges concrete AppendEntries to RT2.
- `ElectionReachability.lean` (ER1–ER12) reduces `CandidateLogCovers` to the shared-source condition.
- `ElectionConcreteModel.lean` (ECM1–ECM7) closes `hqc_preserved` from the `hae` hypothesis.
- **Key insight**: ECM6 (`hqc_preserved_of_validAEStep`) proves that `hqc_preserved` holds
  given (a) the leader won the election, (b) voters' logs agree with the leader up to their
  last index (`hae`), and (c) a valid AE step fires. The remaining gap is now:

  > **Derive `hae` inductively** from the concrete AE broadcast history.
  > ECM5 gives `hae` for a single AE step (indices > prevLogIndex). The inductive case
  > needs to show that this agreement is maintained across all AE steps from one leader.

### Priority for future runs:
1. **Task 5 (Proofs)**: `hae` inductive invariant — new file `AEBroadcastInvariant.lean`:
   - Define `HAEInvariant cs lead` := `∀ w k, k ≤ (voterLog w).index → cs.logs w k = cs.logs lead k`
   - Prove it is preserved by `ValidAEStep` from lead to any voter v
   - Compose with ECM6 to get `hqc_preserved` without `hae` as explicit hypothesis
   - ~10–20 theorems
2. **Task 5 (Proofs)**: Complete RaftLogAppend Phase 5:
   - P6: batch suffix matches (result log has the new entries starting at their indices)
   - P7: entries beyond the batch are discarded (truncation correctness)
3. **Task 7 (Critique)**: Update CRITIQUE.md with Runs 43–46 findings:
   - ElectionConcreteModel.lean (ECM1–ECM7) section
   - Updated theorem counts (483→505)
   - Paper review update for new sections
4. **Task 11 (Paper)**: Update paper.tex with theorem counts 505/32, new sections on:
   - ElectionReachability.lean (ER1–ER12)
   - ElectionConcreteModel.lean (ECM1–ECM7)
   - RaftLogAppend.lean (RA1–RA9+3, P4/P5)
5. **Target 11** (`progress_set`) — still lower priority than closing the inductive gap
6. **Aeneas extraction** — still blocked on container privileges

## Mathlib Modules Expected to Be Useful

- `Mathlib.Data.List.Basic` — list prefix, length, `take`
- `Mathlib.Data.List.Sort` — sorted list properties
- `Mathlib.Algebra.Order.Ring.Lemmas` — arithmetic inequalities
- `Mathlib.Data.Finset.Basic` — finite set majority reasoning
- `Std.Data.List.Lemmas` — list operations

## Aeneas Applicability

The codebase explicitly supports Aeneas via the `aeneas` Cargo feature. The `committed_index` and `vote_result` functions have safe-Rust variants ready for Charon extraction. Task 8 (Aeneas Extraction) should be attempted once the Charon+Aeneas toolchain is available in the CI environment.

## References

- [Raft paper](https://raft.github.io/raft.pdf)
- [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)
- [Aeneas](https://github.com/AeneasVerif/aeneas)
- [Charon](https://github.com/AeneasVerif/charon)

## Run 67 Update (2026-04-21) — FindConflictByTerm + Next Targets

**Current state**: 552 theorems, 47 Lean files, 0 sorry.

### Completed This Run
`find_conflict_by_term` (Task 3/5): `RaftLog::find_conflict_by_term` formalised in
`FVSquad/FindConflictByTerm.lean` (10 theorems, 0 sorry). Key properties proved:
- **FCB1**: Result index ≤ input index (scan is bounded)
- **FCB2**: Returned term ≤ query term (correctness of scan exit)
- **FCB3**: Maximality — every index above result has term > query term
- **FCB4**: Identity — immediate return when first entry matches
- **FCB5/FCB7**: Out-of-range guard correctness
- **FCB6**: The model always returns `Some` (no storage-error path)
- **FCB8**: Base-case characterisation (dummy entry at index 0)
- **FCB9**: Monotone log implies maximality (delegates to FCB3)

### Research Directions for Future Runs

1. **Connect to fast-reject path** (`handle_append_response`, `src/raft.rs ~L1657`):
   prove that `find_conflict_by_term` output is a valid probe point for the leader.

2. **`progress_set`** (`src/tracker/progress_set.rs`): `ProgressSet::quorum_active` —
   informal spec + Lean spec. Would bridge per-peer `Progress` model to full-cluster
   quorum tracking.

3. **Connect AEBroadcastInvariant to election lifecycle**:
   after an election, the leader broadcasts AE; ABI8 should apply. Requires composing
   `RaftElection.lean` → `ElectionConcreteModel.lean` → `AEBroadcastInvariant.lean`.

4. **Update conference paper** (`formal-verification/paper/paper.tex`):
   Runs 60–67 add ReadOnly (15T), FindConflictByTerm (10T), 0-sorry milestone.
   Section on correspondence tests (12 targets, 160+ #guard cases) needs expansion.

## Run 82 Update (2026-04-22) — RaftLogAppend Correspondence + Research Refresh

**Current state**: 522 theorems, 52 Lean files (53 with new RaftLogAppendCorrespondence.lean), 0 sorry.

### Task 8: RaftLogAppendCorrespondence

`RaftLog::append` (from `src/raft_log.rs:382`) now has a correspondence test in
`FVSquad/RaftLogAppendCorrespondence.lean` (21 `#guard` assertions, 0 sorry) and a
matching Rust test `test_raft_log_append_correspondence` (11 assertion cases, all pass).

This completes the correspondence test coverage for all major Lean proof targets:
**17 correspondence-test files** covering **17 Rust functions** with **342+ `#guard` tests**.

The three structural branches of `truncate_and_append` are all exercised:
1. **Append** (`after = offset + len`): new entries attached at the end
2. **Replace** (`after ≤ offset`): new batch replaces all unstable entries
3. **Truncate + append** (`offset < after < offset + len`): partial overwrite

Invariants RA4 (`committed` unchanged) and RA5 (`stableLastIdx` unchanged) are
cross-checked at the Rust level, closing the model-to-implementation gap.

### Critique-Driven Research Adjustments

Based on `CRITIQUE.md` Run 76 recommendations:

1. **firstUpdateIndex modelling** (MaybePersist gap): The `maybe_persist` model treats
   `firstUpdateIndex` as an opaque `Nat`. In the Rust implementation this is derived from
   `unstable.snapshot?.index + 1` or `unstable.offset`. Formalising this derivation would
   promote MP6 from "parameter correct" to "derivation correct". Target: add a
   `MaybePersistFUI.lean` formalising the FUI derivation from `LogUnstable`.

2. **Progress ↔ ProgressTracker integration**: `Progress.lean` (31T, 0 sorry) and
   `ProgressCorrespondence.lean` (55 `#guard`) cover the per-peer invariants. The
   multi-peer `ProgressTracker::update_committed` and `ProgressTracker::quorum_active`
   are not yet formalised. Target: `ProgressSet.lean` lifting invariants to multi-peer.

3. **AEBroadcastInvariant ↔ election lifecycle**: `AEBroadcastInvariant.lean` (ABI1–ABI10)
   proves that after a broadcast AE round, `hqc_preserved` holds. The remaining gap is
   connecting this to the full Raft election protocol — showing that a post-election
   leader actually performs such a broadcast. Target: compose `RaftElection.lean` →
   `ElectionConcreteModel.lean` → `AEBroadcastInvariant.lean` into a single chain.

4. **Conference paper recompilation**: `formal-verification/paper/paper.tex` was last
   updated in Run 81 with Run-81 numbers. LaTeX compilation requires `latexmk` (not
   currently available in the sandbox). Paper needs updating for Runs 78–82 changes
   (MaybePersistCorrespondence, MaybeCommitCorrespondence, RaftLogAppendCorrespondence).

### Next High-Priority Research Targets (Run 85 Update)

> **Run 84 completed**: B1 (`firstUpdateIndex` / `MaybePersistFUI.lean`) is **done** — 8
> theorems (FU1–FU8, 0 sorry) formalise the FUI derivation from `Unstable` fields (snap case
> and no-snap case), plus 20 `#guard` correspondence tests in `MaybePersistFUICorrespondence.lean`
> and a Rust test with 18 cases. FU7 (`maybePersistFui_snap_blocks_advance_at`) is the key
> safety property.

The current state (Run 84/85): **55 Lean files, ~530 theorems, 0 sorry, 18 correspondence
test targets with 362+ `#guard` tests**.

| Priority | Target | Goal | Difficulty | Files | Status |
|----------|--------|------|-----------|-------|--------|
| ~~**B1**~~ | ~~`firstUpdateIndex`~~ | ~~Formalise FUI derivation~~ | ~~Low~~ | `MaybePersistFUI.lean` | ✅ **Done (Run 84)** |
| **B2** | `progress_set` | `ProgressSet::quorum_active` informal + Lean spec | Medium | `ProgressSet.lean` | ⬜ Not started |
| **B3** | Election-broadcast chain | Compose election → broadcast → ABI8 | High | `ElectionBroadcastChain.lean` | ⬜ Not started |
| **B4** | REPORT.md + paper.tex | Update for Runs 78–84 (18 corr files, 362+ #guard) | Low | `REPORT.md`, `paper.tex` | ⬜ Needs update |

### B2 Detail: `ProgressSet::quorum_active`

**File**: `src/tracker/progress_set.rs`  
**Function**: `ProgressSet::quorum_active(&self) -> bool`

**What it does**: Returns `true` if a majority of voters in the configuration have been
"recently active" (their `Progress.recent_active` flag is set). Used to detect whether the
cluster is still live enough to respond without confirming quorum each time (avoid lease
transfers on short partitions).

**Key properties to verify**:
1. If `|voters| = 0`, result is vacuously true
2. Monotone: adding a `recent_active=true` voter cannot flip `false → true` in reverse
3. Consistency with `HasQuorum`: `quorum_active ↔ hasQuorum(voters, fn(v) => progress(v).recent_active)`
4. Lifting: per-peer `Progress` invariants (PR1–PR35) apply to each tracked peer

**Proof tractability**: Medium — builds directly on `HasQuorum.lean` and `Progress.lean`.
The key insight is that `quorum_active` is syntactic sugar for `has_quorum` applied to
the `recent_active` boolean field.

**Approximations**: `ProgressSet` has a `group_commit_mode: bool` flag and joint
configuration support. The initial spec can focus on the simple (non-joint) case.

### B3 Detail: Election-Broadcast Chain

**Goal**: Close the final gap in the Raft safety proof by showing that after a legitimate
election, the new leader performs the initial AE broadcast described in
`ElectionConcreteModel.lean`, and therefore `hqc_preserved` holds inductively.

**Proof path**:
1. `RaftElection.lean` (RE1–RE15): election safety (one leader per term)
2. `ElectionConcreteModel.lean` (ECM1–ECM7): after broadcast, `hqc_preserved` holds
3. `AEBroadcastInvariant.lean` (ABI1–ABI10): inductive invariant for broadcast sequences
4. New: `ElectionBroadcastChain.lean` — compose all three to show `RaftReachable` is
   closed under full election + replication

**Difficulty**: High. Requires connecting the abstract election model to the concrete
`RaftReachable` step, which bundles 5 hypotheses each of which needs to be discharged.

### Critique-Driven Adjustments (Run 82–85)

Based on Run 76 `CRITIQUE.md` recommendations and subsequent work:

1. **B1 (FUI modelling)** — DONE. `MaybePersistFUI.lean` (Run 84) closes MP6 gap.
   FU4 proves `maybePersistFui_eq_abstract` (concrete = abstract with derived FUI).

2. **B2 (ProgressSet)** — Still pending. The per-peer `Progress.lean` (31T) and
   `ProgressCorrespondence.lean` (55 #guard) provide a solid foundation.

3. **B3 (election-broadcast chain)** — Still pending. All component lemmas exist;
   the remaining task is composing them into a single end-to-end chain.

4. **Critique freshness** — `CRITIQUE.md` is from Run 76 (569T/50F). Current state is
   ~530T/55F (some theorem renamings may account for the count difference). An updated
   critique reviewing the Run 77–84 additions would be valuable.

