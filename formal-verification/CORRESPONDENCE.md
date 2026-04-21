# FV Correspondence Map

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This document maps each Lean definition to the Rust source it models.  It records the
correspondence level, known divergences, and the impact on any proofs that rely on the
definition.

## Last Updated
- **Date**: 2026-04-21 00:44 UTC
- **Commit**: `896e159` — Run 48: Task 6 Correspondence Review; added RaftLogAppend.lean and ElectionConcreteModel.lean sections (505 theorems, 32 files)

---

## Correspondence Levels (key)

| Level | Meaning |
|-------|---------|
| **Exact** | Lean function is semantically equivalent to the Rust on all inputs within the stated preconditions. |
| **Abstraction** | Lean function models a pure subset of the Rust semantics; deliberately ignores some aspects (e.g., I/O, mutation, overflow). All ignored aspects are documented. |
| **Approximation** | Lean function is semantically different in some known way; proofs hold only under additional assumptions. |
| **Mismatch** | Lean function diverges from the Rust in a way that could invalidate proofs. |

---

## `formal-verification/lean/FVSquad/LimitSize.lean`

### Target: `limit_size` — `src/util.rs`

Rust source: [`src/util.rs#L54`](../src/util.rs#L54)

#### Lean definitions

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `totalSize` | *(none — auxiliary)* | — | Exact | Pure helper; sum of serialised sizes. No Rust counterpart; derived from `u64::from(e.compute_size())` accumulation. |
| `limitSizeCount` | *(internal `take_while` scan)* | `src/util.rs#L72–80` | Abstraction | Models the `take_while` iterator as structural recursion. Same termination behaviour. |
| `limitSize` | `limit_size` | `src/util.rs#L54` | Abstraction | See divergences below. |

#### Known divergences (Abstraction-level)

1. **Type abstraction** — Rust uses `T: PbMessage + Clone` where `compute_size()` returns `u32` cast to `u64`. Lean uses a generic type `α` with an abstract `size : α → Nat` function. Any proof about `limitSize` holds for *any* `size` function, which is strictly more general.

2. **Numeric types** — Rust uses `u64` for the budget and for running size totals. Lean uses `Nat` (unbounded). Overflow cannot occur in the Lean model. Real Rust code could overflow if `compute_size()` produces values summing past `u64::MAX`, but this is precluded by the `NO_LIMIT = u64::MAX` early-exit guard.

3. **In-place mutation** — Rust calls `entries.truncate(limit)` on a `&mut Vec<T>`. Lean returns a new `List α`. The pure return value matches the post-mutation state of the Rust `Vec`.

4. **`NO_LIMIT` sentinel** — Rust uses the sentinel `u64::MAX` to mean "no limit". Lean unifies `None` and `NO_LIMIT` as `Option.none`. This is correct because the Rust code has `None | Some(NO_LIMIT) => return` on lines 67–69 of `src/util.rs`.

5. **`take_while` semantics** — The Rust `take_while` closure checks `if size == 0 { size += ...; return true }` (always include first). The Lean `limitSizeCount` mirrors this with `if k == 0 then ...` (always recurse with k=1 for the first element). The semantics are equivalent.

#### Impact on proofs

All 17 theorems proved in `LimitSize.lean` rely on `limitSize` and `limitSizeCount`. The divergences above are all safe abstractions:

- Overflow is not modelled (safe: NO_LIMIT guard prevents overflow in practice).
- Mutation is replaced by pure return (safe: semantically equivalent post-state).
- Type abstraction is strictly more general (safe: proofs hold for any `size` function).

The 17 theorems include 5 helper lemmas about `totalSize` and `limitSizeCount`
(`totalSize_take_le`, `limitSizeCount_ge_k`, `limitSizeCount_le_add_length`,
`limitSizeCount_pos`, `limitSizeCount_le_length`) that were added in a later pass to
support the higher-level proofs; plus 12 main theorems about `limitSize` itself.

**Assessment**: The Lean model is a sound abstraction of the Rust. No proofs are invalidated by these divergences, provided the precondition `budget < Nat.max` is respected (vacuously satisfied by `Nat`).

---

## `formal-verification/lean/FVSquad/ConfigValidate.lean`

### Target: `Config::validate` — `src/config.rs`

Rust source: [`src/config.rs#L166`](../src/config.rs#L166)

#### Lean definitions

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `ReadOnlyOption` | `ReadOnlyOption` | `src/read_only.rs` (re-exported) | Exact | Two variants: `Safe`, `LeaseBased`. Rust has the same two variants. |
| `Config` | `Config` | `src/config.rs#L26` | Abstraction | See divergences below. |
| `Config.minTick` | `Config::min_election_tick()` | `src/config.rs#L148–155` | Exact | Identical logic: if `min_election_tick == 0` return `election_tick` else return `min_election_tick`. |
| `Config.maxTick` | `Config::max_election_tick()` | `src/config.rs#L158–164` | Exact | Identical logic: if `max_election_tick == 0` return `2 * election_tick` else return `max_election_tick`. |
| `configValidate` | `Config::validate` | `src/config.rs#L166` | Abstraction | See divergences below. |
| `Config.valid` | *(conceptual — no direct counterpart)* | — | — | Propositional predicate; not present in Rust. |

#### Known divergences (Abstraction-level)

1. **Struct fields omitted** — The Lean `Config` record omits fields not checked by `validate`: `priority`, `batch_append`, `skip_bcast_commit`, `applied`. These have no bearing on validation correctness.

2. **Numeric types** — Rust uses `u64` for `id`, `max_size_per_msg`, `max_uncommitted_size` and `usize` for tick/inflight fields. Lean models all as `Nat`. Overflow is not modelled; in practice, all values are small Raft configuration constants.

3. **Return type** — Rust returns `Result<()>` (either `Ok(())` or `Err(ConfigInvalid(msg))`). Lean models this as `Bool` (`true = Ok`, `false = Err`). Error messages are not captured. This is intentional: the specification focuses on the validity predicate, not error reporting.

4. **Short-circuit evaluation** — Rust returns on the *first* failed constraint. Lean computes all constraints simultaneously as a boolean conjunction. Both produce the same final `Ok`/`Err` classification (though they differ in which error message would be emitted, which the Lean model ignores).

5. **`INVALID_ID = 0`** — Modelled explicitly as `c.id ≠ 0`, matching `src/config.rs` where `INVALID_ID = 0` is defined.

#### Impact on proofs

All 10 theorems proved in `ConfigValidate.lean` focus on the boolean decision function `configValidate` and its equivalence to the propositional `Config.valid`. The divergences are:

- Overflow not modelled (safe: configuration values are never near `u64::MAX`).
- Omitted fields not relevant to validation (safe: proofs only concern the eight checked constraints).
- Bool vs `Result` (safe: only validity, not error messages, is formalised).
- Short-circuit vs full evaluation (safe: same accept/reject outcome).

**Assessment**: The Lean model is a sound abstraction of `Config::validate`. The proofs correctly characterise *when* validation passes or fails.

---

## `formal-verification/lean/FVSquad/MajorityVote.lean`

### Target: `Configuration::vote_result` — `src/quorum/majority.rs`

Rust source: [`src/quorum/majority.rs#L189`](../src/quorum/majority.rs#L189)

#### Lean definitions

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `VoteResult` | `VoteResult` | `src/quorum.rs#L12` | Exact | Three variants: `Pending`, `Lost`, `Won`. Exact match. |
| `majority` | `majority` | `src/util.rs#L123` | Exact | `n / 2 + 1`. Identical formula. |
| `yesCount` / `missingCount` | *(internal loop variables `yes`, `missing`)* | `src/quorum/majority.rs#L197–205` | Exact | Lean uses separate recursive functions; Rust uses a single loop with two counters. Semantically equivalent. |
| `voteResult` | `Configuration::vote_result` | `src/quorum/majority.rs#L189` | Abstraction | See divergences below. |

#### Known divergences (Abstraction-level)

1. **Voter representation** — Rust uses `HashSet<u64>` (unordered, no duplicates). Lean uses `List Nat`. Lean theorems that depend on uniqueness carry an explicit `voters.Nodup` hypothesis. Theorems that do not depend on uniqueness hold for arbitrary lists.

2. **Check function type** — Rust takes `impl Fn(u64) -> Option<bool>`. Lean takes `Nat → Option Bool`. The types are equivalent at the level of pure logic.

3. **Numeric types** — Voter IDs are `u64` in Rust, `Nat` in Lean. No overflow is possible for voter IDs in any realistic scenario.

4. **Empty voter set** — Rust returns `VoteResult::Won` for an empty voter set (by convention, for joint quorum compatibility). Lean matches this exactly.

#### Impact on proofs

Theorems in `MajorityVote.lean` prove properties about `voteResult`. The main caveats are:

- Lean list-based proofs cover multisets (possibly with duplicates); for correspondence with the Rust `HashSet<u64>` semantics, uniqueness (`voters.Nodup`) must be assumed where it matters.
- The `majority` function is proved exact (see `majority_pos`, `majority_gt_half`), so all quorum-size arguments are sound.

**Assessment**: The Lean model is a sound abstraction of `Configuration::vote_result`. The proofs hold under the stated hypotheses.

---

## `formal-verification/lean/FVSquad/JointVote.lean`

### Target: `Configuration::vote_result` (joint) — `src/quorum/joint.rs`

Rust source: [`src/quorum/joint.rs#L63`](../src/quorum/joint.rs#L63)

#### Lean definitions

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `combineVotes` | *(match expression)* | `src/quorum/joint.rs#L68–75` | Exact | Directly mirrors the four-arm `match (i, o)` pattern. Semantically identical. |
| `jointVoteResult` | `Configuration::vote_result` | `src/quorum/joint.rs#L63` | Abstraction | See divergences below. |

#### Known divergences (Abstraction-level)

1. **Voter representation** — Rust `Configuration` holds `incoming: MajorityConfig` and
   `outgoing: MajorityConfig`, each backed by a `HashSet<u64>`. Lean represents these
   as `List Nat` parameters passed directly to `jointVoteResult`, abstracting the struct wrapper.

2. **`outgoing` default** — In a single-group (non-joint) configuration, Rust leaves
   `outgoing` as `MajorityConfig::default()` (empty). Lean's theorem `J4` proves that
   `jointVoteResult incoming [] check = voteResult incoming check`, confirming the
   non-joint case is handled correctly.

3. **Check function sharing** — Rust passes `&check` to `incoming.vote_result` and
   `check` (by move) to `outgoing.vote_result`. In Lean the same `check : Nat → Option Bool`
   function is passed to both calls. This is equivalent because the function is pure.

4. **Numeric types and voter IDs** — Same as `MajorityVote.lean`: `u64` → `Nat`, no overflow.

#### Impact on proofs

- `JointVote.lean` directly reuses the `voteResult` function and all lemmas from
  `MajorityVote.lean`. Its 14 theorems (CL1–CL4, J1–J10) are sound given the
  `MajorityVote.lean` model.
- The `combineVotes` function is a direct structural translation of the Rust `match`; no
  approximation is needed.
- Theorems about symmetry (J9, J10) have no direct Rust counterpart but are natural
  corollaries of the structure.

**Assessment**: The Lean model is a sound abstraction of the joint `vote_result`. The
14 proved theorems fully characterise the joint quorum decision rule.

---

## `formal-verification/lean/FVSquad/CommittedIndex.lean`

### Target: `Configuration::committed_index` — `src/quorum/majority.rs`

Rust source: [`src/quorum/majority.rs#L163`](../src/quorum/majority.rs#L163)

#### Lean definitions

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `sortDesc` | *(Vec sort — `sort_by(b.cmp(a))`)* | `src/quorum/majority.rs#L172` | Exact | Lean uses `List.mergeSort (≥)`; semantically identical descending sort. |
| `sortedAcked` | *(mapped and sorted `matched` vec)* | `src/quorum/majority.rs#L168–175` | Abstraction | Rust collects into a stack array then sorts in-place. Lean maps then sorts. Same output. |
| `committedIndex` | `Configuration::committed_index` | `src/quorum/majority.rs#L163` | Abstraction | Non-group-commit path only. See divergences below. |
| `countGe` | *(no direct counterpart — auxiliary)* | — | — | Declarative characterisation; used in proofs of safety/maximality. |

#### Known divergences (Abstraction-level)

1. **Group-commit path omitted** — Rust has a `use_group_commit = true` branch
   (lines 177–186 of `majority.rs`) that uses group IDs for committed-index computation.
   This branch is **not modelled**. All proved theorems apply to the `use_group_commit = false` path only.

2. **Empty-config return value** — Rust returns `u64::MAX` for an empty voter set
   (so that `min(u64::MAX, x) = x` in joint quorums). Lean returns `0` to stay in `Nat`.
   The divergence is documented in `committedIndex_empty_contract`. Joint-quorum callers
   must handle the empty case separately.

3. **Stack-array optimisation** — The Rust implementation uses an unsafe inline array for
   small voter sets. This is a performance optimisation only; the output is identical to
   a heap-allocated sort. Lean models the heap path (`List`).

4. **Types** — Voter IDs are `u64` → `Nat`; acked indices are `u64` → `Nat`. Overflow not
   modelled. The `AckedIndexer` trait is abstracted as a pure `Nat → Nat` function
   (mapping `None` → `0` via Rust's `unwrap_or_default()`).

5. **Voter list vs. set** — Rust uses an implicit `HashSet`-backed deduplication. Lean uses
   `List Nat` (duplicates assumed absent where they matter for theorems about majority counts).

#### Impact on proofs

All 13 theorems proved in `CommittedIndex.lean` are:

- **sortDesc_length**, **sortDesc_perm**, **sortDesc_pairwise**: structural properties of the sort. Exact correspondence.
- **sortedAcked_length**, **sortedAcked_perm**: structural properties. Exact correspondence.
- **CI1** (`committedIndex_empty`) and **CI1-contract**: correctly capture the 0 vs `u64::MAX` divergence.
- **CI2** (`committedIndex_singleton`): exact for a single voter.
- **CI3–CI7**: properties of `countGe`; sound abstract characterisation.
- **CI8** (`committedIndex_all_zero`): holds under the Lean model.
- **CI-Safety**, **CI-Maximality**: prove that `committedIndex` is the largest index acknowledged by a majority. These are the key correctness properties; they hold for the non-group-commit path.
- **CI-Monotonicity**: acked-index non-decrease → committed-index non-decrease. Key liveness property.

**Assessment**: The Lean model is a sound abstraction of `Configuration::committed_index`
for the non-group-commit path. The Safety and Maximality theorems provide meaningful
confidence in the sort-then-index algorithm's correctness. No mismatches found.

---

No mismatches found. All six Lean models are sound abstractions of their Rust counterparts.

---

## `formal-verification/lean/FVSquad/FindConflict.lean`

### Target: `RaftLog::find_conflict` — `src/raft_log.rs`

Rust source: [`src/raft_log.rs#L195`](../src/raft_log.rs#L195)

#### Lean definitions

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `LogEntry` | `Entry` (protobuf) | `proto/eraftpb.proto` | Abstraction | Lean captures only `index` and `term`; payload bytes are not modelled. |
| `LogTerm` | *(combined `RaftLog` stable + unstable store)* | `src/raft_log.rs` | Abstraction | Rust splits log storage across `RaftLog.store` and `RaftLog.unstable`; Lean abstracts both as a single `Nat → Option Nat` (index → term) function. |
| `matchTerm` | `RaftLog::match_term` | `src/raft_log.rs#L248` | Abstraction | Rust: `term(idx).map_or(false, |t| t == term)`. Lean: `match log idx with | some t => t == term | none => false`. Semantically identical (both return `false` for out-of-range indices). |
| `findConflict` | `RaftLog::find_conflict` | `src/raft_log.rs#L201` | Abstraction | See divergences below. |

#### Known divergences (Abstraction-level)

1. **Entry payload omitted** — Rust `Entry` is a protobuf message carrying `data`, `context`,
   `entry_type`, etc.  Lean `LogEntry` stores only `index` and `term`.  The `find_conflict`
   function only inspects `index` and `term` (via `match_term`), so this omission does not
   affect the semantic correctness of the model.

2. **Log storage split** — The real `RaftLog` stores entries in two regions:
   `self.store` (stable, via the `Storage` trait) and `self.unstable` (in-memory append
   buffer).  The Lean model unifies these as a single `LogTerm` function.  The Rust
   `match_term` method transparently queries both regions; the Lean `matchTerm` mirrors the
   observable behaviour, not the internal storage layout.

3. **Error handling** — Rust `term(idx)` returns `Result<u64, Error>`.  An `Err` result
   (e.g., storage I/O failure) causes `match_term` to return `false` via
   `unwrap_or_default()`.  Lean models this by returning `none` (→ `matchTerm` returns
   `false`) for any index not present.  Panics or storage errors are not modelled.

4. **Logging side effects** — The Rust implementation logs a diagnostic message when a
   conflict is found at or below `last_index()`.  This has no semantic effect and is not
   modelled.

5. **Index type** — Raft indices are `u64` in Rust; Lean uses `Nat` (unbounded). Overflow
   is not modelled (safe in practice: log indices never exceed ~2^63 in realistic
   deployments).

6. **Positive-index precondition** — Lean theorems FC4b and FC11 require
   `∀ e ∈ ents, 0 < e.index` to distinguish the "no conflict" sentinel (0) from a
   genuine index-0 entry.  Raft log indices start at 1 by convention; this precondition
   is always satisfied by the Rust caller.  It is an explicit precondition in Lean rather
   than enforced by a type invariant.

#### Impact on proofs

All 12 theorems in `FindConflict.lean` are:

- **FC1–FC3**: definitional lemmas; exact correspondence.
- **FC4a / FC4b**: "all match ↔ result is 0" — hold under the stated positive-index
  precondition.  The precondition is always met by real Raft callers.
- **FC5+FC6 (combined as `findConflict_nonzero_witness`)**: existence of the first
  mismatching entry.  Sound under the Abstraction model.
- **FC7 (`findConflict_first_mismatch`)**: first-mismatch characterisation.  The most
  precise correctness statement; holds exactly under the Lean model.
- **FC8 (`findConflict_skip_match_prefix`)**: transparency of a matching prefix.  Sound.
- **FC9–FC10**: singleton cases.  Exact.
- **FC11 (`findConflict_zero_iff_all_match`)**: biconditional combining FC4a and FC4b.
  The most useful single theorem for downstream reasoning.
- **FC12 (`findConflict_result_in_indices`)**: result is an entry's index.  Sound.

**Assessment**: No mismatches found.  The Lean model is a sound Abstraction of
`RaftLog::find_conflict`.  The payload and storage-split omissions are appropriate and
documented.  All 12 theorems are valid under the stated model and preconditions.

---

No mismatches found. All six Lean models are sound abstractions of their Rust counterparts.

---

## `formal-verification/lean/FVSquad/JointCommittedIndex.lean`

### Target: `joint_committed_index` -- `src/quorum/joint.rs#L47`

*Note: this target was listed as "Planned" in previous versions of this document but has since been completed (phase 5, 10 theorems proved, merged).*

Rust source: [`src/quorum/joint.rs#L47`](../src/quorum/joint.rs#L47)

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `jointCommittedIndex` | `Configuration::committed_index` (joint) | `src/quorum/joint.rs#L47` | Abstraction | `min(incoming_ci, outgoing_ci)` using `CommittedIndex.committedIndex`; `use_group_commit=false` only |

**Known divergences**: same as `CommittedIndex.lean` plus: empty-config path returns 0 in Lean, Rust returns `u64::MAX` (documented in JCI9-JCI10).

**Theorems proved** (10 total, 0 sorry): JCI1-JCI3 (bound lemmas), JCI4-JCI5 (safety for incoming/outgoing), JCI6 (maximality), JCI7 (monotonicity), JCI8-JCI10 (degenerate/empty cases).

**No mismatches found.** All divergences are documented Abstractions.

---

### `maybe_append` — `src/raft_log.rs#L267`

Rust source: [`src/raft_log.rs#L267`](../src/raft_log.rs#L267)

**Lean model**: `formal-verification/lean/FVSquad/MaybeAppend.lean`

**Correspondence**: Abstraction

| Lean name | Rust equivalent | Rust location | Correspondence | Notes |
|-----------|-----------------|---------------|----------------|-------|
| `RaftState` | `RaftLog` fields: `entries`, `committed`, `persisted` | `src/raft_log.rs#L38–L60` | Abstraction | Only `log`, `committed`, `persisted` modelled; stable storage, logger, `applied` omitted |
| `LogTerm` (`Nat → Option Nat`) | `RaftLog::term(idx)` | `src/raft_log.rs#L168` | Abstraction | Log represented as index→term function; entry payload and stable/unstable split omitted |
| `logWithEntries` | `RaftLog::append(suffix)` | `src/raft_log.rs#L338` | Abstraction | Models the pure index→term update; does not model Vec allocation, stable storage write, or truncation beyond last entry |
| `applyConflict` | conflict branch in `maybe_append` | `src/raft_log.rs#L281–L290` | Abstraction | Combines find-suffix and logWithEntries into one step |
| `maybeAppend` | `RaftLog::maybe_append` | `src/raft_log.rs#L267` | Abstraction | See divergences below |

**Divergences (all Abstraction level, no Mismatches)**:

1. **Stable/unstable storage split omitted**: Rust splits entries between `stable_entries` and
   `unstable`. The Lean model uses a single abstract `LogTerm` function. The `persisted` index
   tracks the stable boundary. *Impact*: proofs about `persisted` rollback (MA10–MA12) are
   sound; proofs about storage-level operations are out of scope.

2. **`conflict ≤ committed` panic not modelled**: Rust panics if `find_conflict` returns an
   index ≤ `committed`. The Lean model assumes this case does not arise (it is a safety invariant
   that Raft's leader adherence guarantees). *Impact*: MA13–MA16 assume `conflict > committed`
   implicitly via the Raft protocol.

3. **`Nat` vs `u64`**: Log indices are `Nat` in Lean vs `u64` in Rust. Overflow is not modelled.
   *Impact*: safe given practical log size bounds.

4. **Entry payload omitted**: `LogEntry` has only `index` and `term`; Rust `Entry` also has
   `entry_type`, `data`, `context`, etc. *Impact*: content of entries is irrelevant to the
   correctness properties proved here.

5. **`commit_to` range check omitted**: Rust panics if `to_commit > last_index()`. Lean uses
   `max` to enforce monotonicity without a range guard. *Impact*: safe since `min(ca, lastNew) ≤ lastNew`.

**Theorems proved** (18 total, 0 sorry):

| ID | Property | Level |
|----|----------|-------|
| MA1–MA4 | Return value correctness (None/Some with conflict, lastNew) | High |
| MA5–MA9 | Committed index: exact formula, monotonicity, upper bounds, equality | High |
| MA10–MA12 | Persisted index: no-conflict no-op, rollback, preservation | Mid |
| MA13 | Log prefix preserved (entries before conflict unchanged) | High |
| MA14 | Suffix entries applied (new log has suffix entry terms) | High |
| MA15 | No-conflict: log unchanged | Mid |
| MA16 | Failure: entire state unchanged | Mid |

**No mismatches found.** All divergences are documented Abstractions.

---

## Summary

| Lean file | Rust target | Correspondence level | Proved theorems | Gaps |
|-----------|-------------|---------------------|-----------------|------|
| `LimitSize.lean` | `src/util.rs` `limit_size` | Abstraction | 25 | Overflow not modelled (safe); lint clean ✅ |
| `ConfigValidate.lean` | `src/config.rs` `Config::validate` | Abstraction | 10 | Error messages not captured (by design) |
| `MajorityVote.lean` | `src/quorum/majority.rs` `vote_result` | Abstraction | 21 | Duplicates in voter list not excluded by type |
| `JointVote.lean` | `src/quorum/joint.rs` `vote_result` | Abstraction | 14 | Struct wrapper abstracted; non-joint degeneration proved (J4) |
| `CommittedIndex.lean` | `src/quorum/majority.rs` `committed_index` | Abstraction | 28 | group-commit path omitted; empty→0 (Rust→MAX) documented |
| `FindConflict.lean` | `src/raft_log.rs` `find_conflict` | Abstraction | 12 | Entry payload omitted; positive-index precondition explicit |
| `JointCommittedIndex.lean` | `src/quorum/joint.rs` `committed_index` | Abstraction | 10 | `use_group_commit=false` path only; empty→0 (Rust→MAX) documented |
| `MaybeAppend.lean` | `src/raft_log.rs` `maybe_append` | Abstraction | 18 | Stable/unstable split abstracted; panic not modelled; Nat vs u64 |
| `Inflights.lean` | `src/tracker/inflights.rs` `Inflights` | Abstraction | 49 | Abstract (List) + concrete (InflightsConc) models; ALL correspondence theorems proved (0 sorry); phase 5 complete |
| `Progress.lean` | `src/tracker/progress.rs` `Progress` | Abstraction | 31 | `PendingSnapshot` variant abstracted to single index; async effects omitted |
| `IsUpToDate.lean` | `src/raft_log.rs` `RaftLog::is_up_to_date` | Abstraction | 17 | Log viewed as (term, index) pairs; persistent/unstable split not modelled |
| `LogUnstable.lean` | `src/log_unstable.rs` `Unstable` | Abstraction | 37 | I/O (persist/stable) not modelled; wf Case-2 caller guarantee documented |
| `TallyVotes.lean` | `src/tracker.rs` `ProgressTracker::tally_votes` | Abstraction | 28 | HashMap→function; JointConfig→List; mutation→pure return |

**Total: 300 public theorems/lemmas, 0 sorry, 13 Lean files (+ `Basic.lean`).**

---

## `formal-verification/lean/FVSquad/Inflights.lean` *(phase 5 -- complete)*

### Target: `Inflights` -- `src/tracker/inflights.rs`

Rust source: [`src/tracker/inflights.rs`](../src/tracker/inflights.rs)

#### Lean definitions — Abstract model (`Inflights`)

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `Inflights` (structure) | `Inflights` | `src/tracker/inflights.rs#L18` | Abstraction | Ring buffer abstracted as `{ queue : List Nat, cap : Nat }` |
| `Inflights.add` | `Inflights::add` | `src/tracker/inflights.rs#L64` | Abstraction | Appends to queue tail; ring-buffer index arithmetic omitted |
| `dropLeq` / `Inflights.freeTo` | `Inflights::free_to` | `src/tracker/inflights.rs#L77` | Abstraction | Drops prefix ≤ `to`; `maybe_free_buffer` omitted |
| `Inflights.freeFirstOne` | `Inflights::free_first_one` | `src/tracker/inflights.rs#L101` | Abstraction | `freeTo` applied to head element |
| `Inflights.reset` | `Inflights::reset` | `src/tracker/inflights.rs#L110` | Exact | Clears queue; `cap` preserved |

#### Lean definitions — Concrete ring-buffer model (`InflightsConc`, Task 4)

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `InflightsConc` (structure) | `Inflights` | `src/tracker/inflights.rs#L18` | Exact (structure) | Fields: `buffer : List Nat`, `start`, `count`, `cap` mirror Rust fields |
| `InflightsConc.new` | `Inflights::new` | `src/tracker/inflights.rs#L34` | Exact | Initialises with all zeros; Lean uses `List.replicate` |
| `extractRing` | *(implicit in field access)* | ring-buffer layout | Exact (model) | Extracts `count` elements from `start`, wrapping at `cap` |
| `InflightsConc.addConc` | `Inflights::add` | `src/tracker/inflights.rs#L64` | Abstraction | Sets `(start+count)%cap`; uses `List.set`; `buffer.capacity` not tracked |
| `freeCount` + `InflightsConc.freeToConc` | `Inflights::free_to` | `src/tracker/inflights.rs#L77` | Abstraction | `freeCount` counts leading ≤-to entries; advances `start`; `maybe_free_buffer` omitted |
| `InflightsConc.freeFirstOneConc` | `Inflights::free_first_one` | `src/tracker/inflights.rs#L101` | Exact | `freeToConc` applied to head element |
| `InflightsConc.resetConc` | `Inflights::reset` | `src/tracker/inflights.rs#L110` | Abstraction | Clears count and start; buffer content unchanged (no-op semantically) |
| `InflightsConc.toAbstract` | *(abstraction function)* | — | — | Maps concrete to abstract: `{ queue := logicalContent, cap := cap }` |

#### Known divergences

1. **Ring-buffer `buffer` as `List Nat`**: Rust uses `Vec<u64>` (growable); Lean uses fixed-length `List Nat` (`length = cap`). No capacity growth tracked.
2. **`incoming_cap` / `set_cap`**: Dynamic capacity changes not modelled.
3. **`u64` → `Nat`**: No overflow modelled.
4. **Panics omitted**: `add` panics on full; Lean precondition `count < cap` rules this out.
5. **Sortedness not enforced by type**: Abstract model INF8/INF9 take sortedness as a hypothesis. Concrete model `InflightsConc` also does not enforce sortedness.

#### Correspondence theorems (phase 5 — all proved, 0 sorry)

| Theorem | Status | Meaning |
|---------|--------|---------|
| `inflightsConc_reset_correct` | ✅ proved | `resetConc ↔ reset` via `toAbstract` |
| `inflightsConc_add_correct` | ✅ **proved** | `addConc ↔ add` via `toAbstract`; proved using `listGet_set_eq`, `extractRing_append_last`, `ring_positions_ne` |
| `inflightsConc_freeTo_correct` | ✅ **proved** | `freeToConc ↔ freeTo` via `toAbstract`; proved using `extractRing_dropLeq_eq`, `freeCount_le` |

Key helper lemmas proved in this run:
- `listGet_set_eq` / `listGet_set_ne`: get-set axioms for `List.set`
- `extractRing_succ` / `extractRing_mod_start` / `extractRing_append_last`: structural properties of `extractRing`
- `ring_positions_ne`: ring-buffer position distinctness (positions `(start+i)%cap` for `i ≤ count < cap` are all distinct)
- `extractRing_set_indep`: modifying a position not accessed by extractRing leaves it unchanged
- `freeCount_le`: `freeCount ≤ count`
- `extractRing_dropLeq_eq`: `dropLeq to (extractRing buf cap count start) = extractRing buf cap (count-freed) ((start+freed)%cap)`

The two `sorry`'d theorems are sound in intent — their statements are correct — but the proofs require:
- `listGet (List.set l i v) j = listGet l j` for `j ≠ i` (get-set axiom)
- `listGet (List.set l i v) i = v` for `i < l.length` (get-set same)
- Modular arithmetic around `freeCount` iterating the buffer

These will be addressed in Task 5.

#### Impact on proofs

All 38 proved theorems (INF1–INF32 minus the 2 sorry'd) are sound. The abstract model theorems (INF1–INF18) are fully proved and do not depend on any ring-buffer model. The concrete model structural theorems (INF19–INF29, INF32) are fully proved. The two sorry'd theorems (INF30, INF31) are clearly stated and their proofs are blocked only on get-set arithmetic.

---

> 🔬 Generated by [Lean Squad](https://github.com/dsyme/fv-squad/actions/runs/23714161005) automated formal verification.

---

## `Progress.lean` ↔ `src/tracker/progress.rs`

**Lean file**: `formal-verification/lean/FVSquad/Progress.lean`  
**Rust file**: [`src/tracker/progress.rs`](src/tracker/progress.rs)  
**Phase**: 5 ✅ (31 theorems, 0 sorry)

### Type mapping

| Lean type/def | Rust type/field | Correspondence | Notes |
|---|---|---|---|
| `ProgressState.Probe` | `ProgressState::Probe` | Exact | Default state |
| `ProgressState.Replicate` | `ProgressState::Replicate` | Exact | Fast-path state |
| `ProgressState.Snapshot` | `ProgressState::Snapshot` | Exact | Recovery state |
| `Progress.matched` | `Progress::matched` | Exact | `Nat` vs `u64` |
| `Progress.next_idx` | `Progress::next_idx` | Exact | `Nat` vs `u64` |
| `Progress.state` | `Progress::state` | Exact | |
| `Progress.paused` | `Progress::paused` | Exact | |
| `Progress.pending_snapshot` | `Progress::pending_snapshot` | Exact | |
| `Progress.ins_full` | `Progress::ins.full()` | **Abstraction** | Only `full()` observable property is modelled; ring buffer internals are omitted |
| `Progress.pending_request_snapshot` | `Progress::pending_request_snapshot` | Exact | |
| *(omitted)* | `Progress::recent_active` | **Omitted** | Pure metadata; no invariants involving it |
| *(omitted)* | `Progress::commit_group_id` | **Omitted** | Not part of state machine |
| *(omitted)* | `Progress::committed_index` | **Omitted** | Separate monotone counter |

### Function mapping

| Lean function | Rust function | Correspondence | Divergences |
|---|---|---|---|
| `Progress.mk_new` | `Progress::new` | Abstraction | `ins_size` parameter omitted; `ins_full = false` |
| `Progress.becomeProbe` | `Progress::become_probe` | Exact | |
| `Progress.becomeReplicate` | `Progress::become_replicate` | Exact | |
| `Progress.becomeSnapshot` | `Progress::become_snapshot` | Exact | |
| `Progress.maybeUpdate` | `Progress::maybe_update` | Exact | Returns `(Progress, Bool)` pair vs `&mut self` + `bool` |
| `Progress.maybeDecrTo` | `Progress::maybe_decr_to` | Exact | Nat subtraction saturates at 0; Rust u64 guard proved equivalent (PR26) |
| `Progress.isPaused` | `Progress::is_paused` | Abstraction | `ins.full()` replaced by `ins_full : Bool` |
| `Progress.isSnapshotCaughtUp` | `Progress::is_snapshot_caught_up` | Exact | |
| `Progress.resume` / `Progress.pause` | `Progress::resume` / `Progress::pause` | Exact | |

### Known divergences

1. **Nat vs u64**: All indices are modelled as `Nat` (unbounded).
2. **`ins_full` abstraction**: Ring buffer internals omitted; only `full()` is modelled.
3. **`Progress::reset`**: Not modelled.

### Proved theorems summary

All 31 theorems proved (0 sorry). Key: `wf` invariant (`matched+1≤next_idx`) established by `mk_new` and preserved by all transitions. `becomeProbe`/`becomeReplicate` are self-healing.

> 🔬 Updated by Lean Squad run [23790628468](https://github.com/dsyme/fv-squad/actions/runs/23790628468).

---

## `IsUpToDate.lean` ↔ `src/raft_log.rs`

**Lean file**: `formal-verification/lean/FVSquad/IsUpToDate.lean`  
**Rust file**: [`src/raft_log.rs`](src/raft_log.rs)  
**Phase**: 5 ✅ (18 theorems, 0 sorry)

### Type mapping

| Lean type/def | Rust type/field | Correspondence | Notes |
|---|---|---|---|
| `LogId` | `RaftLog<T>` (last_term, last_index fields) | Abstraction | Only `last_term()` and `last_index()` are modelled; storage, unstable log, commit/apply state all omitted |
| `LogId.term` | `RaftLog::last_term()` | Exact | `Nat` vs `u64` |
| `LogId.index` | `RaftLog::last_index()` | Exact | `Nat` vs `u64` |
| `isUpToDate voter ct ci` | `raft_log.is_up_to_date(last_index, term)` | Exact | Pure function; models only the comparison, not the full `RaftLog` |

### Function mapping

| Lean function | Rust function | Correspondence | Divergences |
|---|---|---|---|
| `isUpToDate` | `RaftLog::is_up_to_date` | Exact | `Nat` instead of `u64`; no overflow possible for practical log sizes |

### Known divergences

1. **Nat vs u64**: All indices and terms are `Nat`. No overflow analysis.
2. **Pure function**: `RaftLog` is a rich struct with storage, commit index, etc. We model only the `(last_term, last_index)` pair needed for the comparison.

### Proved theorems summary

All 18 theorems proved (0 sorry). Key results:
- Correctness: `isUpToDate ↔ logGe` (lex order on term×index)
- Reflexivity, totality, transitivity, antisymmetry
- High-term/low-term/same-term specialisations
- Election restriction: same-term check implies index ≥

> 🔬 Updated by Lean Squad run [23790628468](https://github.com/dsyme/fv-squad/actions/runs/23790628468).

---

## Target: `log_unstable` — `Unstable` struct in `src/log_unstable.rs`

**Lean file**: `formal-verification/lean/FVSquad/LogUnstable.lean`
**Rust source**: `src/log_unstable.rs`
**Phase**: 5 ✅ (37 theorems, 0 sorry)
**Informal spec**: `formal-verification/specs/log_unstable_informal.md`

### Lean model

```lean
structure Unstable where
  offset   : Nat
  entries  : List Nat         -- terms; entries[i].index = offset + i
  snapshot : Option (Nat × Nat)  -- some (snap_index, snap_term) or none
```

### Function mapping

| Lean function | Rust function | Correspondence | Divergences |
|---|---|---|---|
| `maybeFirstIndex` | `Unstable::maybe_first_index` | Exact | `Nat` instead of `u64` |
| `maybeLastIndex` | `Unstable::maybe_last_index` | Exact | `Nat` instead of `u64` |
| `maybeTerm` | `Unstable::maybe_term` | Abstraction | Entry payloads omitted (only terms tracked) |
| `stableEntries` | `Unstable::stable_entries` | Abstraction | Pre-condition (non-empty entries with matching term/index) assumed, not checked; panic path omitted |
| `stableSnap` | `Unstable::stable_snap` | Abstraction | Pre-condition (snapshot present with matching index) assumed |
| `restore` | `Unstable::restore` | Exact | `Nat` instead of `u64`; `Snapshot` struct flattened to `(index, term)` |
| `truncateAndAppend` | `Unstable::truncate_and_append` | Abstraction | `entries_size` accounting omitted; `must_check_outofbounds` not modelled |
| `slice` | `Unstable::slice` | Abstraction | Returns terms only (not full entries); bounds check not modelled |

### Known divergences

1. **Nat vs u64**: All indices/terms are `Nat`. No overflow analysis.
2. **Entry payloads**: Only terms are stored; entry data bytes are omitted.
3. **entries_size**: The Rust tracks byte sizes for flow control; the Lean model ignores this field.
4. **Panic paths**: `stable_entries` panics if entries are empty or the term/index don't match; `stable_snap` panics if no snapshot is present. These pre-conditions are **assumed** in the Lean model (happy path only).
5. **Logger**: The `logger` field and all fatal! calls are omitted.

### Open question from informal spec

`truncate_and_append` in **Case 2** (`after ≤ offset`) changes the offset but does not check
that the snapshot is None. The Rust `stable_entries` asserts `snapshot.is_none()` before
stabilising entries, but `truncate_and_append` does not. The `wf` invariant
(`snapshot.index < offset`) can be violated in Case 2 if a snapshot is pending.
Callers appear to guarantee the snapshot is cleared first, but this is not enforced
by the Rust type system. Captured in `formal-verification/specs/log_unstable_informal.md`.

### Proved theorems summary

All 37 theorems proved (0 sorry). Coverage:

| Group | Theorems | What is proved |
|-------|---------|----------------|
| `maybeFirstIndex` | MFI1–MFI2 | None when no snapshot; Some(idx+1) when snapshot present |
| `maybeLastIndex` | MLI1–MLI3 | None/snapshot/entries correctness |
| `maybeTerm` | MT1–MT5 | Before-offset (no snap, hit, miss); in-entries hit/miss |
| `stableEntries` | SE1–SE5 | Offset advances, entries cleared, snapshot preserved, strict monotonicity |
| `stableSnap` | SS1–SS3 | Snapshot cleared, entries/offset preserved |
| `restore` | RE1–RE7 | Offset=idx+1, empty entries, snapshot set, maybeLastIndex/FirstIndex, maybeTerm correctness |
| `truncateAndAppend` | TAA1–TAA7 | Case 1 (append), Case 2 (replace), Case 3 (truncate+append) entries/offset/length; snapshot always preserved |
| `slice` | SL1 | `(slice u lo hi).length = hi - lo` |
| Well-formedness | WF1–WF4 | `restore_wf`, `stableEntries_wf`, `stableSnap_wf`, Case-1 wf preservation |

> �� Updated by Lean Squad run [23861228143](https://github.com/dsyme/fv-squad/actions/runs/23861228143).

---

## `FVSquad/TallyVotes.lean` ↔ `src/tracker.rs`

### Target: `ProgressTracker::tally_votes`

**Rust source**: `src/tracker.rs` (lines ~301–321)
**Lean file**: `formal-verification/lean/FVSquad/TallyVotes.lean`
**Correspondence level**: *abstraction*

The Lean model abstracts the `ProgressTracker` to its essential voting state:
a list of voter IDs and a pure check function `Nat → Option Bool`.

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `noCount` | `rejected` counter | `tracker.rs:~306` | exact | Counts `Some false` entries |
| `tallyVotes` | `tally_votes` | `tracker.rs:303` | abstraction | Returns `(granted, rejected, result)` |
| `yesCount` (from MajorityVote) | `granted` counter | `tracker.rs:~305` | exact | Counts `Some true` entries |
| `voteResult` (from MajorityVote) | `vote_result` call | `tracker.rs:319` | exact | Via `Configuration::vote_result` |

### Known abstractions

1. **HashMap → function**: `votes: HashMap<u64, bool>` is modelled as `Nat → Option Bool`. Non-voter entries in the Rust map are silently ignored in both the Rust code and the model (the Rust code checks `self.conf.voters.contains(id)` before counting).
2. **JointConfig → List Nat**: The Lean model uses a simple list rather than a `JointConfig` (which combines incoming and outgoing quorum sets). The joint case follows by composition with `JointVote.lean`.
3. **No mutation**: The Lean model is pure; the Rust counts via mutable `granted`/`rejected` variables.
4. **u64 → Nat**: No overflow modelled; not relevant for vote counts in practice.

### Impact on proofs

The key theorem TV12 (`tallyVotes_lost_of_rejected_ge`) is the primary safety property:
if rejected ≥ majority(n), the election is definitively Lost. This holds in both the Lean
model and the Rust code because the counting logic is identical (filter to voters, count
yes/no separately). The abstraction of `HashMap` to a function does not affect this property.

### Proved theorems summary

All 18 theorems proved (0 sorry). Coverage:

| Group | Theorems | What is proved |
|-------|---------|----------------|
| Projections | TV1–TV3 | Correct components (granted=yesCount, rejected=noCount, result=voteResult) |
| Bounds | TV4–TV6 | granted ≤ n, rejected ≤ n, granted+rejected ≤ n |
| Partition | TV7 | granted + rejected + missing = voters.length (exact partition) |
| Edge cases | TV8 | Empty voters → (0, 0, Won) |
| Iff characterisations | TV9–TV10, TV17 | Won/Lost/Pending iff conditions |
| Safety | TV11–TV12 | granted ≥ majority → Won; rejected ≥ majority → Lost |
| Exhaustiveness | TV13 | Result is one of Won/Pending/Lost |
| Positive voting | TV14 | At least one vote cast → granted+rejected > 0 |
| Extreme cases | TV15–TV16 | All-yes → (n, 0, Won); all-no → (0, n, Lost) |
| No double-quorum | TV18 | Won and Lost cannot hold simultaneously |

---

## `FVSquad/SafetyComposition.lean` ↔ `src/quorum/majority.rs` + `src/tracker.rs`

**Lean file**: `formal-verification/lean/FVSquad/SafetyComposition.lean`
**Rust sources**: [`src/quorum/majority.rs`](src/quorum/majority.rs), [`src/tracker.rs`](src/tracker.rs)
**Phase**: 5 ✅ (9 theorems, 0 sorry)

This file contains no Lean models of Rust functions — it is a **pure composition layer**
that connects independently proved modules (`CommittedIndex`, `HasQuorum`,
`QuorumRecentlyActive`).  There is no direct Rust function corresponding to any single
theorem here; instead, the theorems formalise properties that emerge from the interaction
of Rust subsystems.

### Correspondence notes

| Lean concept | Rust concept | Correspondence | Notes |
|---|---|---|---|
| `SC4_raft_log_safety` | §5.3 safety argument in Raft paper | Abstraction | Formalises the quorum-intersection argument; no single Rust function |
| `SC6_committedIndex_quorum_iff` | `AckedIndexer` + `Configuration::committed` | Abstraction | Biconditional characterising `committed_index` via quorum predicate |
| `SC9_quorumActive_and_commit_share_voter` | Leader election + commit quorum | Abstraction | Models leader-election safety; no single Rust function |

### Known divergences

1. **AckedFn = Nat → Nat**: The Rust uses `AckedIndexer` trait (with `HashMap` backing). Modelled as pure function.
2. **Voter list vs HashSet**: `List Nat` vs `HashSet<u64>`. `Nodup` not enforced.
3. **No mutation**: All theorems are about functional models.

### Proved theorems summary

All 9 theorems proved (0 sorry). SC4 is the key cross-module result: two committed indices
share a witness voter. SC6 is the biconditional bridge. SC9 proves leader election safety.

---

## `FVSquad/JointSafetyComposition.lean` ↔ `src/quorum/joint.rs` + `src/quorum/majority.rs`

**Lean file**: `formal-verification/lean/FVSquad/JointSafetyComposition.lean`
**Rust sources**: [`src/quorum/joint.rs`](src/quorum/joint.rs), [`src/quorum/majority.rs`](src/quorum/majority.rs)
**Phase**: 5 ✅ (10 theorems, 0 sorry)

Like `SafetyComposition`, this file is a pure composition layer. It extends SC4 to
joint-quorum configurations (Rust: `JointConfig { incoming, outgoing }`).

### Correspondence notes

| Lean concept | Rust concept | Correspondence | Notes |
|---|---|---|---|
| `JSC7_joint_raft_log_safety` | `JointConfig` safety argument | Abstraction | Requires witnesses in both quorum halves |
| `JSC1_jointCI_le_iff` | `JointConfig::committed` logic | Abstraction | `min(ci_in, ci_out)` iff both quorums certify |

### Known divergences

1. **Empty outgoing**: `committedIndex [] _ = 0` in Lean, `u64::MAX` in Rust. Theorems JSC3–JSC7 require non-empty lists.
2. **Joint config as `(List Nat) × (List Nat)`**: Rust `JointConfig` has richer metadata.
3. **Voter list vs HashSet**: Same as SafetyComposition.

### Proved theorems summary

All 10 theorems proved (0 sorry). JSC7 is the main result; JSC8–JSC10 prove monotonicity
and edge cases for the joint committed index.

---

## `FVSquad/CrossModuleComposition.lean` ↔ `src/raft_log.rs` + `src/quorum/majority.rs`

**Lean file**: `formal-verification/lean/FVSquad/CrossModuleComposition.lean`
**Rust sources**: [`src/raft_log.rs`](src/raft_log.rs), [`src/quorum/majority.rs`](src/quorum/majority.rs)
**Phase**: 5 ✅ (7 theorems, 0 sorry)

This file bridges the log-operation layer (`MaybeAppend`, `FindConflict`) to the quorum
layer (`CommittedIndex`, `SafetyComposition`). No individual Lean function models a
specific Rust function; the theorems express cross-layer invariants.

### Correspondence notes

| Lean theorem | Rust invariant | Correspondence | Notes |
|---|---|---|---|
| `CMC3_maybeAppend_committed_bounded` | Commit-index bounded by quorum | Abstraction | `maybe_append` never commits beyond what a majority has acknowledged |
| `CMC6_committed_index_entry_bridge` | `committed_index ≥ k → ∃ quorum entry` | Abstraction | Bridge from index to log-entry existence |
| `CMC7_maybeAppend_safety_composition` | Log-entry uniqueness after replication | Abstraction | Composes RSS1 + CMC6 |

### Known divergences

1. **AckedFn vs `RaftLog::acked_applied_index`**: Rust uses `RaftLog`; modelled as `Nat → Nat`.
2. **Commit value as nat**: Rust `committed_to` is `u64` with sentinel `0`. Modelled as `Nat`.

### Proved theorems summary

All 7 theorems proved (0 sorry). CMC3 is the central result: `maybe_append` is safe
(never commits beyond the quorum certificate).

---

## `FVSquad/RaftSafety.lean` — Abstract Raft Safety Layer

**Lean file**: `formal-verification/lean/FVSquad/RaftSafety.lean`
**Rust sources**: no single Rust file; models the **protocol-level safety guarantees**
of the Raft consensus algorithm as implemented across `src/`
**Phase**: 5 ✅ (14 theorems + 2 key definitions, 0 sorry)

This file lifts quorum-level results to log-entry-level safety theorems. It defines:
- `VoterLogs E`: `Nat → Nat → Option E` — per-voter log as a function
- `ClusterState E`: structure with `voters : List Nat` and `logs : VoterLogs E`
- `isQuorumCommitted`: a majority of voters have the same entry at a given index
- `CommitCertInvariant`: every applied entry was certified by a quorum
- `nodeHasApplied`: `logs v k = some e` (voter `v` has committed entry `e` at index `k`)

### Type/definition mapping

| Lean type/def | Rust concept | Correspondence | Notes |
|---|---|---|---|
| `VoterLogs E` | `RaftLog::entries` per peer | Abstraction | Only term×entry, no storage, unstable, commit metadata |
| `ClusterState E` | Raft cluster snapshot | Abstraction | Static snapshot; no network, timing, or leadership |
| `isQuorumCommitted` | Raft commit rule | Abstraction | Encodes the majority-quorum commit criterion |
| `CommitCertInvariant` | Protocol safety invariant | Abstraction | The key invariant whose preservation implies Raft safety |
| `nodeHasApplied` | `RaftLog::applied` | Abstraction | `logs v k = some e`; ignores actual apply semantics |

### Known divergences

1. **Static snapshot model**: `ClusterState` is a snapshot, not a transition system. Protocol dynamics (terms, leader election, timeouts) are not modelled at this layer.
2. **CommitCertInvariant as hypothesis**: RSS6/RSS7 take CCI as a hypothesis; RSS8 delegates to `RaftTrace.lean` for the inductive proof.
3. **Nat vs u64**: All indices and terms are `Nat`.
4. **No network**: Message passing, retransmission, and partitions are omitted.
5. **LogMatchingInvariantFor / NoRollbackInvariantFor**: These are Lean predicates expressing temporal protocol invariants; the correspondence to the Rust protocol is the subject of `RaftProtocol.lean`.

### Proved theorems summary

All 14 theorems proved (0 sorry). RSS1/RSS2 are the core log-entry-level safety theorems.
RSS6/RSS7 are the conditional end-to-end cluster safety theorems. RSS8 is the unconditional
end-to-end theorem, proved via `CommitCertInvariant` from `RaftTrace.lean`.

---

## `FVSquad/RaftProtocol.lean` — Protocol Transition Invariants

**Lean file**: `formal-verification/lean/FVSquad/RaftProtocol.lean`
**Rust sources**: [`src/raft_log.rs`](src/raft_log.rs), [`src/raw_node.rs`](src/raw_node.rs)
**Phase**: 5 ✅ (10 theorems, 0 sorry)

This file models Raft protocol transitions and proves that `LogMatchingInvariant` (LMI)
and `NoRollbackInvariant` (NRI) are preserved by AppendEntries and RequestVote steps.

### Type/function mapping

| Lean type/def | Rust concept | Correspondence | Notes |
|---|---|---|---|
| `RaftTransition` | AppendEntries / RequestVote RPCs | Abstraction | Two-constructor inductive type; omits term management, heartbeats |
| `AppendEntriesArgs` | `AppendEntries` RPC | Abstraction | `idx, term, entries, committed`: core fields only |
| `LogMatchingInvariantFor E logs` | Raft log-matching invariant (§5.3) | Abstraction | Predicate on `VoterLogs E`; no time or network |
| `NoRollbackInvariantFor E voters logs₀ logs₁` | Raft no-rollback guarantee (§5.4.2) | Abstraction | Between two log snapshots; captures `hno_truncate` condition |

### Key divergences

1. **Abstract transitions**: `RaftTransition` does not include term tracking, leader
   validation, log consistency checks performed by Raft — only the structural effects on
   log state. The proof obligations (`hleader_lmi`, `hno_truncate`) must be established
   by callers from more concrete models.
2. **Single voter step**: RP8 models a single AppendEntries to a single voter. Multi-step
   proofs follow by induction via `RaftTrace.lean`.
3. **Leader LMI as hypothesis**: `appendEntries_preserves_log_matching` (RP6) takes
   `hleader_lmi` (the leader's post-append log is LMI-compatible with the cluster) as a
   hypothesis. This captures the Raft election-safety invariant informally.
4. **hno_truncate as hypothesis**: RP8 requires `conflict > committed`; this corresponds
   to the Rust `maybe_append` panic assertion. The panic path is not modelled — it is
   excluded by precondition.

### Proved theorems summary

All 10 theorems proved (0 sorry). RP6 (three cases) and RP8 are the primary results.
RP6 is the Log Matching Property preservation theorem; RP8 is the no-rollback theorem.

---

## `FVSquad/RaftTrace.lean` — Reachability and Top-Level Safety

**Lean file**: `formal-verification/lean/FVSquad/RaftTrace.lean`
**Rust sources**: Protocol semantics of `src/` (Raft consensus algorithm)
**Phase**: 5 ✅ (3 theorems + `RaftReachable` inductive type, 0 sorry)

This is the **capstone file**. It defines an inductive reachability predicate
`RaftReachable` and proves unconditional end-to-end safety.

### Type/definition mapping

| Lean type/def | Concept | Correspondence | Notes |
|---|---|---|---|
| `RaftReachable cs` | "cs is a reachable Raft cluster state" | Abstraction | Inductive predicate; `step` constructor bundles invariant-preservation conditions |
| `initialCluster voters` | Empty initial cluster | Exact | `logs = fun _ _ => none`, `committed = fun _ => 0` |
| `RaftReachable.init` | Fresh cluster startup | Abstraction | Initial state satisfies CCI vacuously |
| `RaftReachable.step` | One Raft protocol step | Abstraction | Five named hypotheses capture invariant conditions abstractly |

### RaftReachable.step hypotheses vs Rust guarantees

| Hypothesis | What it expresses | Rust correspondence |
|---|---|---|
| `hlogs'` | Only one voter's log changes | Single-voter `AppendEntries` application |
| `hno_overwrite` | Committed entries not overwritten | `maybe_append` panic-guard (`conflict > committed`) |
| `hqc_preserved` | Quorum-certified entries preserved in all logs | Leader Completeness Property (Raft §5.4.1) |
| `hcommitted_mono` | Committed indices only advance | `committed_to` monotone in `maybe_append` |
| `hnew_cert` | New committed entries are quorum-certified | Commit rule: advance only after quorum ACK |

### Known divergences

1. **Abstract step hypotheses**: `RaftReachable.step` does not model concrete Raft
   transitions (no term tracking, no leader election, no vote counting). The step
   hypotheses are proof-engineering artefacts that precisely capture what's needed to
   preserve `CommitCertInvariant`, but their correspondence to real Raft transitions is
   informal. This is the honest residual gap in the FV portfolio.
2. **Single-step model**: Each `step` applies to one voter changing one log. Concurrent
   steps or batched AppendEntries are not modelled.
3. **No liveness**: `RaftReachable` does not model leader election progress or liveness
   guarantees — only safety.

### Proved theorems summary

All 3 theorems proved (0 sorry).

| Theorem | What it proves |
|---|---|
| `initialCluster_cci` (RT0) | Initial cluster satisfies `CommitCertInvariant` (vacuous: no entries committed) |
| `raftReachable_cci` (RT1) | Every reachable state satisfies `CommitCertInvariant` (induction on `RaftReachable`) |
| `raftReachable_safe` (RT2) | Every reachable cluster state is safe (RT1 + RSS8) |

RT2 is the **top-level safety theorem** for the FVSquad portfolio. It asserts: for any
cluster state reachable via valid Raft transitions, no two voters ever apply different
entries at the same log index.

---

## `FVSquad/HasQuorum.lean` ↔ `src/tracker.rs` — `has_quorum`

**Lean file**: `formal-verification/lean/FVSquad/HasQuorum.lean`
**Rust source**: [`src/tracker.rs#L357`](../src/tracker.rs#L357)
**Phase**: 5 ✅ (20 theorems, 0 sorry)

Models `ProgressTracker::has_quorum` — determines whether a set of node IDs forms a majority
quorum of the current voter list.

### Type/definition mapping

| Lean name | Rust name | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `overlapCount` | *(inner filter count)* | `src/tracker.rs#L357` | Exact | Counts voters in `potential_quorum`; equivalent to `HashSet::get` iteration |
| `intersectCount` / `unionCount` | *(set-arithmetic helpers)* | — | Exact | Pure auxiliaries for quorum intersection proofs |
| `hasQuorum` | `ProgressTracker::has_quorum` | `src/tracker.rs#L357` | Abstraction | See divergences below |

### Known divergences (Abstraction-level)

1. **`HashSet<u64>` → `Nat → Bool`** — The potential quorum is modelled as a membership
   predicate rather than a hash set. Any Rust hash set yields such a predicate; the
   abstraction is sound.
2. **`u64` → `Nat`** — No overflow modelled; voter IDs and counts are far below 2⁶³.
3. **`voters` uniqueness** — Rust maintains voters as a deduplicated list. The Lean model
   allows duplicates; uniqueness is stated as an explicit precondition in proofs that
   require it (HQ14, HQ20).
4. **`JointConfig` not modelled here** — The joint-quorum variant is modelled in
   `JointVote.lean` and `JointTally.lean`; this file covers only the majority path.

### Impact on proofs

HQ20 (`quorum_intersection_mem`) produces an explicit shared voter and is used by
`RaftElection.lean` (RE4) and `LeaderCompleteness.lean` (LC1). The full 20-theorem set
(HQ1–HQ20) covers empty/singleton cases, monotonicity, and inclusion-exclusion.

**Assessment**: Abstraction is sound. Uniqueness assumption is documented and enforced
at use sites.

---

## `FVSquad/JointTally.lean` ↔ `src/tracker.rs` — `tally_votes` (joint)

**Lean file**: `formal-verification/lean/FVSquad/JointTally.lean`
**Rust source**: [`src/tracker.rs#L303`](../src/tracker.rs#L303)
**Phase**: 5 ✅ (18 theorems, 0 sorry)

Models `ProgressTracker::tally_votes` for the joint-quorum case — when `self.conf.voters`
is a `JointConfig` with non-empty `incoming` and `outgoing` halves.

### Type/definition mapping

| Lean name | Rust name | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `jointTallyVotes` | `ProgressTracker::tally_votes` (joint path) | `src/tracker.rs#L303` | Abstraction | See divergences |

### Known divergences (Abstraction-level)

1. **Double-counting of overlap voters** — If a voter `v` appears in both `incoming` and
   `outgoing` (which the real `JointConfig` prohibits by invariant), the Lean model counts
   `v`'s vote twice. Theorems that depend on this state `no_overlap` as an explicit
   precondition (JT14).
2. **`u64` → `Nat`** — No overflow.

### Impact on proofs

JT1–JT4 are the primary results (result, Won/Lost/Pending characterisations); JT5 connects
the joint tally to the single-quorum tally when `outgoing = []`.

**Assessment**: Abstraction is sound for well-formed joint configs (disjoint halves).

---

## `FVSquad/LogUnstable.lean` ↔ `src/log_unstable.rs`

**Lean file**: `formal-verification/lean/FVSquad/LogUnstable.lean`
**Rust source**: [`src/log_unstable.rs`](../src/log_unstable.rs)
**Phase**: 5 ✅ (37 theorems, 0 sorry)

Models the `Unstable` struct — the not-yet-persisted (in-memory) segment of the Raft log —
and its key query and mutation operations.

### Type/definition mapping

| Lean name | Rust name | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `Unstable` | `Unstable` struct | `src/log_unstable.rs#L1` | Abstraction | Terms only; payload fields omitted |
| `maybeFirstIndex` | `Unstable::maybe_first_index` | `src/log_unstable.rs` | Exact | Snapshot index + 1 |
| `maybeLastIndex` | `Unstable::maybe_last_index` | `src/log_unstable.rs` | Exact | Last entry or snapshot index |
| `maybeTerm` | `Unstable::maybe_term` | `src/log_unstable.rs` | Exact | Term at a given index |
| `truncate` / `append` / `stableTo` | mutation operations | `src/log_unstable.rs` | Abstraction | Pure return value; no mutation |

### Known divergences (Abstraction-level)

1. **Terms only** — Rust entries hold arbitrary `Entry` payloads; Lean entries are `Nat` terms only.
2. **Pure functions** — Rust methods mutate `self`. Lean models return new `Unstable` values.
3. **Panic paths omitted** — Fatal-log conditions are excluded by preconditions.
4. **`u64` → `Nat`** — No overflow.
5. **`entries_size` not modelled** — Byte-size accounting is irrelevant to correctness.

### Impact on proofs

37 theorems covering query correctness, round-trip properties (stableTo / append), and
boundary conditions. Foundational lemmas for log-correctness properties in the wider portfolio.

**Assessment**: Abstraction is sound. Term-only model is sufficient for all targeted properties.

---

## `FVSquad/MaybeAppend.lean` ↔ `src/raft_log.rs` — `maybe_append`

**Lean file**: `formal-verification/lean/FVSquad/MaybeAppend.lean`
**Rust source**: [`src/raft_log.rs#L267`](../src/raft_log.rs#L267)
**Phase**: 5 ✅ (18 theorems, 0 sorry)

Models `RaftLog::maybe_append` — the AppendEntries receiver logic that conditionally
appends leader entries to the follower's log after finding any conflict point.

### Type/definition mapping

| Lean name | Rust name | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `MaybeAppendState` | `RaftLog` fields subset | `src/raft_log.rs#L267` | Abstraction | `{ log, committed, persisted }` |
| `maybeAppend` | `RaftLog::maybe_append` | `src/raft_log.rs#L267` | Abstraction | Pure model; see divergences |

### Known divergences (Abstraction-level)

1. **Abstract log** — Rust uses a concrete `RaftLog` with stable/unstable split. Lean uses
   `Nat → Option Nat` (index → optional term); both storage layers merged.
2. **Panic path omitted** — `conflict ≤ committed` triggers `fatal!` in Rust. Excluded
   by precondition; proofs cover only the success path.
3. **Consecutive entries assumption** — `ents[k].index = idx + 1 + k` stated as explicit
   precondition.
4. **`u64` → `Nat`** — No overflow.

### Impact on proofs

The `conflict > committed` panic guard in Rust is the enforcement of `hno_overwrite` in
`RaftReachable.step`; `MaybeAppend.lean` formalises the conditions under which it holds.

**Assessment**: Abstraction is sound. The panic-exclusion precondition matches the Rust
caller contract exactly.

---

## `FVSquad/QuorumRecentlyActive.lean` ↔ `src/tracker.rs` — `quorum_recently_active`

**Lean file**: `formal-verification/lean/FVSquad/QuorumRecentlyActive.lean`
**Rust source**: [`src/tracker.rs#L336`](../src/tracker.rs#L336)
**Phase**: 5 ✅ (11 theorems, 0 sorry)

Models `ProgressTracker::quorum_recently_active` — checks whether a quorum of voters
have recently been active from the perspective of a given leader node.

### Type/definition mapping

| Lean name | Rust name | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `isActive` | *(inline logic)* | `src/tracker.rs#L336–354` | Abstraction | Leader always active + recent_active flag |
| `quorumRecentlyActive` | `ProgressTracker::quorum_recently_active` | `src/tracker.rs#L336` | Abstraction | Read semantics only; write side-effects omitted |

### Known divergences (Abstraction-level)

1. **Write side-effects omitted** — The Rust function sets `recent_active := false` on
   non-leader nodes. The Lean model captures only the return value.
2. **`HashMap` → `List (Nat × Progress)`** — Modelled as an association list; duplicates
   allowed (the real Rust has unique-keyed map maintained by configuration change machinery).
3. **`u64` → `Nat`** — No overflow.

### Impact on proofs

QRA15 (monotonicity) ensures more active entries never decreases the quorum check result.

**Assessment**: Abstraction is sound. The write-side-effect omission does not affect
the correctness of the proven properties.

---

## `FVSquad/CommitRule.lean` — Raft Commit Rule

**Lean file**: `formal-verification/lean/FVSquad/CommitRule.lean`
**Rust source**: Commit logic distributed across `src/raft.rs` and `src/raft_log.rs`
**Phase**: 5 ✅ (9 theorems, 0 sorry)

Formalises the **Raft commit rule** abstractly: a leader advances `committed` to index `k`
only when a quorum of followers have confirmed entry `k`.

### Type/definition mapping

| Lean name | Rust concept | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `MatchIndexQuorum` | leader's per-voter `matchIndex` tracking | `src/tracker.rs` (`Progress.matched`) | Abstraction | Predicate: quorum of voters have `matchIndex ≥ k` |
| `CommitRuleValid cs cs'` | commit advance validity condition | distributed in `src/raft.rs` | Abstraction | Definitionally equal to `hnew_cert` in `RaftReachable.step` |

### Known divergences

1. **Distributed commit logic** — The Rust commit rule is enforced across `maybe_commit`
   and `tally_votes`. The Lean model captures only the quorum-ACK condition; term-safety
   (A6) is in `MaybeCommit.lean`.
2. **Abstract `matchIndex`** — `Progress.matched` (`u64`) modelled as `Nat`.

### Impact on proofs

CR8 proves `CommitRuleValid cs cs'` is definitionally equal to `hnew_cert` in
`RaftReachable.step`, directly discharging that proof obligation. CR9 shows that the
commit rule plus log preservation implies `CommitCertInvariant` is preserved.

**Assessment**: Abstraction-level. The CR8 bridge is definitional — no assumptions added.

---

## `FVSquad/MaybeCommit.lean` ↔ `src/raft_log.rs` — `maybe_commit` / `commit_to`

**Lean file**: `formal-verification/lean/FVSquad/MaybeCommit.lean`
**Rust source**: [`src/raft_log.rs#L530`](../src/raft_log.rs#L530) and [`src/raft_log.rs#L304`](../src/raft_log.rs#L304)
**Phase**: 5 ✅ (12 theorems, 0 sorry)

Models `RaftLog::maybe_commit` and `RaftLog::commit_to` — the functions that advance the
committed index with the A6 term-safety check.

### Type/definition mapping

| Lean name | Rust name | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `maybeCommit` | `RaftLog::maybe_commit` | `src/raft_log.rs#L530` | Abstraction | Abstract log `Nat → Option Nat`; see divergences |
| `commitTo` | `RaftLog::commit_to` | `src/raft_log.rs#L304` | Exact | Modelled as `max committed toCommit` (panic excluded) |

### Known divergences (Abstraction-level)

1. **Abstract log** — Same as `MaybeAppend.lean` (no storage split).
2. **`zero_term_on_err_compacted` abstracted** — Rust returns 0 for compacted entries;
   Lean uses `log k = some term` directly; compacted-entry handling excluded by
   precondition.
3. **`fatal!` panic path omitted** — `commit_to` panics if `toCommit > lastIndex`.
4. **`u64` → `Nat`** — No overflow.

### Impact on proofs

MC4 (`maybeCommit_term`) is the primary result: **A6 term safety** — if `maybeCommit`
advances `committed`, the entry at the new committed index has the term supplied as argument
(the leader's current term). This directly formalises Raft §5.4.2 and closes the A6
obligation. MC12 shows `maybeCommit = commitTo` when the term check passes.

**Assessment**: Abstraction is sound. MC4 is the critical A6 closure theorem.

---

## `FVSquad/ConcreteTransitions.lean` — AppendEntries Model and HLogConsistency (A4)

**Lean file**: `formal-verification/lean/FVSquad/ConcreteTransitions.lean`
**Rust source**: AppendEntries receiver in `src/raft_log.rs` and `src/raft.rs`
**Phase**: 5 ✅ (11 theorems, 0 sorry)

Provides a concrete AppendEntries RPC message type, a pure application function, and
proves `HLogConsistency` from the protocol invariants.

### Type/definition mapping

| Lean name | Rust concept | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `AppendEntriesMsg E` | AppendEntries RPC | `src/raft.rs` (message types) | Abstraction | Core fields: `prevLogIndex`, `prevLogTerm`, `entries`, `leaderCommit` |
| `applyAppendEntries` | `RaftLog::maybe_append` receiver path | `src/raft_log.rs#L267` | Abstraction | Term-stripped; models log update only |
| `CandLogMatching` | Log Matching Property (leader-side) | distributed in `src/raft_log.rs` | Abstraction | Candidate log agrees with every voter at all shared indices |
| `CandLogCoversLastIndex` | Leader log coverage condition | — | Abstraction | Candidate log covers each voter's last index |

### Known divergences (Abstraction-level)

1. **Term stripping** — `applyAppendEntries` operates on term-only logs; payload content
   not verified.
2. **Single-step model** — One AE message to one follower per step.
3. **AE acceptance as precondition** — Full AE rejection path not modelled.

### Impact on proofs

CT1 establishes `HLogConsistency` from `CandLogMatching + CandLogCoversLastIndex`.
CT5b/CT6 close the A4 path: concrete protocol transitions → `HLogConsistency`.
These results are used by `LeaderCompleteness.lean` (LC7/LC8) and `ConcreteProtocolStep.lean`
(CPS13).

**Assessment**: Abstraction is sound. The `HLogConsistency` result is the key A4 deliverable.

---

## `FVSquad/ConcreteProtocolStep.lean` — A5 Bridge (ValidAEStep → RaftReachable)

**Lean file**: `formal-verification/lean/FVSquad/ConcreteProtocolStep.lean`
**Rust source**: AppendEntries protocol in `src/raft.rs` and `src/raft_log.rs`
**Phase**: 5 ✅ (14 theorems, 0 sorry)

The **A5 bridge**: given a single concrete valid AppendEntries step (`ValidAEStep`), the
resulting cluster state is `RaftReachable`.

### Type/definition mapping

| Lean name | Rust concept | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `ValidAEStep E cs cs'` | One valid AE transaction | `src/raft.rs` + `src/raft_log.rs` | Abstraction | Bundles structural + commit-rule conditions |
| `validAEStep_raftReachable` (CPS2) | AE protocol step preserves reachability | — | Abstraction | Central A5 bridge theorem |
| `validAEStep_hqc_preserved_from_lc` (CPS13) | `hqc_preserved` discharge | — | Abstraction | Via `CandidateLogCovers` + `HasQuorum.monotone` + `LeaderCompleteness` |

### ValidAEStep hypotheses vs Rust conditions

| Hypothesis | What it expresses | Rust correspondence |
|---|---|---|
| `hvoter` | Follower `v` is in voter list | `prs.contains(v)` |
| `hlog'` | New log is AE application | `maybe_append` success path |
| `hno_overwrite` | Committed prefix unchanged | `conflict > committed` panic guard |
| `hcommitted_mono` | Committed indices advance | `commit_to` monotonicity |
| `hnew_cert` | New commits are quorum-certified | commit rule (via `CommitRule.lean`) |
| `hqc_preserved` | QC entries remain in all logs | Leader Completeness (via `LeaderCompleteness.lean`) |

### Known divergences (Abstraction-level)

1. **No term management** — `ValidAEStep` does not model Raft term tracking; term safety
   (A6) is handled separately by `MaybeCommit.lean`.
2. **Single-voter step** — One AE application to one follower per step.
3. **`hqc_preserved` weakened** — In run 41, `hqc_preserved` was weakened to a log-agreement
   form that simplifies discharging from concrete transitions. This is a deliberate modelling
   choice.

### Impact on proofs

CPS2 (`validAEStep_raftReachable`) shows any `ValidAEStep` on a `RaftReachable` state
produces another `RaftReachable` state. CPS13 discharges `hqc_preserved` using
`CandidateLogCovers` from `LeaderCompleteness`.

**Assessment**: Abstraction-level. Every `ValidAEStep` hypothesis corresponds to a concrete
Rust condition. The residual gap is showing `ValidAEStep` is satisfied by the real
`src/raft.rs` message-handling loop (requires a full state-machine model).

---

## `FVSquad/RaftElection.lean` ↔ `src/raft.rs` — Election model

**Lean file**: `formal-verification/lean/FVSquad/RaftElection.lean`
**Rust source**: [`src/raft.rs#L63`](../src/raft.rs#L63) (StateRole), [`src/raft.rs#L163`](../src/raft.rs#L163) (Raft struct fields)
**Phase**: 5 ✅ (15 theorems, 0 sorry)

Models the Raft leader election mechanism (§5.2) and proves ElectionSafety: at most one
candidate wins per term.

### Type/definition mapping

| Lean name | Rust name | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `NodeRole` | `StateRole` | `src/raft.rs#L63` | Exact | Three variants: Follower / Candidate / Leader |
| `NodeState` | `Raft` struct (subset) | `src/raft.rs#L163–188` | Abstraction | `currentTerm`, `votedFor`, `role` only |
| `VoteRecord` | `HashMap<u64, bool>` votes | `src/tracker.rs` | Abstraction | Modelled as function `Nat → Nat → Option Nat` (automatically single-valued) |
| `wonInTerm` | *(election outcome via `tally_votes`)* | `src/tracker.rs` | Abstraction | Predicate: majority quorum voted for candidate |
| `voteGranted` | vote-request handler | `src/raft.rs` | Abstraction | Guards: `votedFor` check + `isUpToDate` condition |

### Known divergences (Abstraction-level)

1. **Heavy abstraction** — Omits log entries, committed index, message queues, election
   timers, `prs` (progress tracker), heartbeat tracking, leadership transfer, randomised
   election timeout.
2. **`VoteRecord` as a function** — Rust uses `HashMap<u64, bool>`; Lean uses `Nat → Nat
   → Option Nat` (automatically single-valued per voter per term, making the Raft
   one-vote-per-term invariant structural rather than assumed).
3. **`votedFor : Option Nat`** — Rust uses `u64` with 0 as `INVALID_ID` sentinel.
4. **`u64` → `Nat`** — No overflow.

### Impact on proofs

RE5 (`electionSafety`) is the primary result: at most one candidate wins per term. RE7
(`voteGranted_isUpToDate`) links election victory to `isUpToDate`, feeding into
`LeaderCompleteness.lean`.

**Assessment**: Abstraction is sound. The function representation of `VoteRecord` makes
the single-vote invariant structural.

---

## `FVSquad/LeaderCompleteness.lean` — Leader Completeness Property (Raft §5.4.1)

**Lean file**: `formal-verification/lean/FVSquad/LeaderCompleteness.lean`
**Rust source**: Protocol semantics of `src/raft.rs` (vote granting) and AppendEntries
**Phase**: 5 ✅ (10 theorems, 0 sorry)

Formalises the Raft **Leader Completeness** property (§5.4.1): an elected leader has all
quorum-committed entries in its log. Provides the discharge condition for `hqc_preserved`
in `RaftReachable.step`.

### Type/definition mapping

| Lean name | Rust concept | Rust location | Correspondence | Notes |
|---|---|---|---|---|
| `VoteRecordConsistency` | Invariant: votes cast via `voteGranted` | `src/raft.rs` vote handler | Abstraction | Predicate: all recorded votes satisfy `voteGranted` |
| `CandidateLogCovers` | Leader has all committed entries | — | Abstraction | Winning candidate's log agrees with voters who voted |
| `HLogConsistency` | Log Matching Property (candidate-side) | Raft §5.3 | Abstraction | isUpToDate → candidate has all voter entries |
| `leaderCompleteness` (LC3) | Leader Completeness §5.4.1 | — | Abstraction | Winner has all committed entries |

### Known divergences (Abstraction-level)

1. **`CandidateLogCovers` and `HLogConsistency` as hypotheses** — Taken as preconditions;
   `ConcreteTransitions.lean` (CT5b/CT6) supplies them from the concrete AE broadcast model.
2. **Election model abstraction** — Uses `RaftElection.lean`'s `wonInTerm` / `VoteRecord`;
   full protocol state (term management, message delays) not modelled.

### Impact on proofs

LC3 (`leaderCompleteness`) is the central result. LC6 (`hqc_preserved_from_leaderBroadcast`)
directly provides the discharge condition for `hqc_preserved` in `RaftReachable.step`.
LC8 (`leaderCompleteness_via_logMatching`) gives the full chain: LMI + VRC + HLogConsistency
→ Leader Completeness.

**Assessment**: Abstraction-level. The conditional structure (hypotheses vs derived facts)
is honest; the proofs show *that* leader completeness implies `hqc_preserved`, and separately
*that* concrete AE steps imply leader completeness.

---

## `FVSquad/RaftLogAppend.lean` — RaftLog::append (14 theorems, 0 sorry)

**Lean file**: `formal-verification/lean/FVSquad/RaftLogAppend.lean`
**Rust source**: [`src/raft_log.rs#L382`](../src/raft_log.rs#L382)
**Phase**: 5 ✅ (14 theorems, 0 sorry)

Formalises `RaftLog::append` from `src/raft_log.rs` (line 382).  Imports and reuses
`FVSquad/LogUnstable.lean` for the `Unstable`, `truncateAndAppend`, and `maybeTerm`
definitions.

### Type/definition mapping

| Lean name | Rust name | Rust location | Correspondence | Notes |
|-----------|-----------|---------------|----------------|-------|
| `RaftLog` | `RaftLog<T>` | `src/raft_log.rs` | Abstraction | `committed`, `stableLastIdx`, `unstable` fields only; `applied`, `max_next_offset` omitted |
| `Entry` | `eraftpb::Entry` | `src/raft_log.rs` | Abstraction | `(index, term)` pair only; payload/context omitted |
| `raftLastIndex` | `RaftLog::last_index` | `src/raft_log.rs#L202` | Exact | Returns unstable last index if non-empty, else stable last index |
| `raftLogAppend` | `RaftLog::append` | `src/raft_log.rs#L382` | Abstraction | Success path only; see divergences |
| `taa_maybeTerm_before` (RA-PFIX1) | `Unstable::truncate_and_append` monotonicity | `src/raft_log.rs#L382` | Exact | Monotonicity property of `truncateAndAppend` |
| `ra_committed_prefix_preserved` (RA-PFIX3) | Intent of `if after < committed { fatal!() }` guard | `src/raft_log.rs#L393` | Exact | Machine-checked proof that the panic guard achieves its stated purpose |

### Known divergences (Abstraction-level)

1. **Panic path omitted** — `RaftLog::append` calls `fatal!()` if `ents[0].index - 1 < committed`
   (line 393).  The Lean model covers only the success path; the panic path is excluded.
   This is documented and conservative: `ra7_committed_below_return` (RA7) and
   `ra_committed_prefix_preserved` (RA-PFIX3) both take `committed < first.1` as a
   precondition, mirroring the guard.
2. **Entry payload omitted** — `Entry` is modelled as `(index, term)` only.  Payload
   (`data`, `context`, `entry_type`) is omitted.  All prefix-preservation proofs hold
   independently of payload.
3. **`u64` → `Nat`** — No overflow.  In Rust, `ents[0].index` is `u64`; in Lean it is `Nat`.
   All theorems hold only in the no-overflow regime (i.e., `Nat` semantics).
4. **Stable storage is read-only** — `stableLastIdx` is a constant in the Lean model;
   the actual Rust `RaftLog` has a `Storage` trait interface.  The model focuses on
   the unstable-segment operations that `append` performs.
5. **Logger / tracing side effects omitted** — Lean model is pure functional.

### Impact on proofs

The 14 theorems provide complete postcondition coverage for the success path of
`RaftLog::append`:

- **RA1–RA9**: basic API correctness (no-op on empty, return value, committed immutability,
  snapshot isolation).
- **RA-PFIX1** (`taa_maybeTerm_before`): monotonicity of `truncateAndAppend` — entries
  before the batch start are not touched.  Proved across all three cases of `truncateAndAppend`.
- **RA-PFIX2** (`ra_prefix_preserved`): lifts RA-PFIX1 to the `raftLogAppend` level.
- **RA-PFIX3** (`ra_committed_prefix_preserved`): proves that the panic guard (`committed < first.1`)
  guarantees committed entries are never modified.  This is the machine-checked proof that
  the Rust `fatal!` guard achieves its stated safety purpose.

**Assessment**: Abstraction-level (success path only).  All divergences are documented and
conservative.  No proved theorem is invalidated by the omission of the panic path — the
theorems are stated with the appropriate precondition.

---

## `FVSquad/ElectionConcreteModel.lean` — Concrete Election + AE Broadcast (8 theorems, 0 sorry)

**Lean file**: `formal-verification/lean/FVSquad/ElectionConcreteModel.lean`
**Rust source**: `src/raft.rs` (election protocol), `src/raft_log.rs` (AE handling)
**Phase**: 5 ✅ (8 theorems, 0 sorry)
**Depends on**: `ConcreteProtocolStep.lean` (CPS13), `ElectionReachability.lean` (ER9/ER10)

Provides the concrete election model that closes the `hqc_preserved` gap in the
`RaftReachable.step` proof chain.  All theorems are abstract compositions of previously
proved results; no new Rust concepts are introduced beyond those in the upstream files.

### Type/definition mapping

| Lean name | Rust concept | Rust location | Correspondence | Notes |
|-----------|--------------|---------------|----------------|-------|
| `hae` hypothesis | Post-broadcast log agreement | `src/raft_log.rs` AE handler | Abstraction | `∀ w k, k ≤ (voterLog w).index → logs w k = candLog k`; models the effect of a successful AE broadcast round |
| ECM1 `candLogCoversLastIndex_of_hae` | Leader completeness (via shared source) | — | Abstraction | Derives abstract CandLogCoversLastIndex from `hae` via ER9 |
| ECM2 `candLogMatching_of_hae` | Log-matching from broadcast | — | Abstraction | Reuses CT5; concrete broadcast model |
| ECM3 `candidateLogCovers_of_hae` | CandidateLogCovers from `hae` | — | Abstraction | Combines ECM1 + ECM2 + hconsist via ER10 |
| ECM4 `hqc_preserved_of_hae` | hqc_preserved from `hae` | — | Abstraction | CPS13 ∘ ECM3 |
| ECM5 `hae_of_validAEStep` | AE step gives log agreement | `src/raft_log.rs#L382` + AE msg | Abstraction | `ValidAEStep.hcand_eq` is exactly the `hae` condition for newly covered indices |
| ECM5b `hae_other_of_validAEStep` | Non-target voters unchanged | — | Exact | Structural consequence of `ValidAEStep.hlogs'_other` |
| ECM6 `hqc_preserved_of_validAEStep` | Full hqc_preserved discharge | — | Abstraction | Primary export: composition of ECM3+ECM4 with `ValidAEStep` |
| ECM7 `sharedSource_of_hae` | Explicit shared-source witness | — | Abstraction | Documentation: `R = candLog`; exposes the shared-source reference for auditing |

### Known divergences (Abstraction-level)

1. **`hae` is an assumption, not derived** — ECM6 takes `hae` as a hypothesis.  In a
   concrete Raft protocol, `hae` would be derived by induction over the AE broadcast history
   (`AEBroadcastInvariant.lean`, the next target in TARGETS.md).  This is the only remaining
   gap in the proof chain.
2. **Single AE step** — ECM5 and ECM6 are stated for a single `ValidAEStep`.  A real Raft
   protocol involves many AE rounds; the inductive argument over rounds is the obligation
   that `hae` encapsulates.
3. **`voterLog` is abstract** — The function `voterLog : Nat → LogId` maps each voter to
   their last accepted log ID.  In Rust, this is tracked via `nextIndex`/`matchIndex` in
   `ProgressTracker` (`src/tracker.rs`); the Lean model abstracts this away.

### Impact on proofs

ECM6 (`hqc_preserved_of_validAEStep`) is the primary export: it proves the `hqc_preserved`
hypothesis required by `RaftReachable.step` directly from a concrete `ValidAEStep` plus
the `hae` agreement condition.  This closes the last major gap in the proof chain:

```
hae (log agreement hypothesis)
    + ValidAEStep (concrete AE step)
    ↓ ECM3 + ECM4 (via CPS13 + ER10)
hqc_preserved ✅
    ↓ CPS2 (via RaftReachable.step)
RaftReachable.step → RT1 → RT2
    ↓
raftReachable_safe ✅
```

ECM5 (`hae_of_validAEStep`) bridges the concrete AE step to the `hae` condition for
newly covered indices, showing that `ValidAEStep.hcand_eq` is precisely the per-step
increment of the `hae` invariant.

**Assessment**: Abstraction-level.  The `hae` hypothesis is honest: it is a well-defined
abstract condition (not a vague assumption), and deriving it by induction over AE rounds
is a tractable next step (~10–20 theorems in `AEBroadcastInvariant.lean`).

---

## Known Mismatches

No known mismatches as of this update.  All 32 Lean models are at *abstraction* or *exact*
level.  The honest residual gaps are:

1. **`hae` hypothesis not yet derived inductively** — ECM6 proves `hqc_preserved` conditional
   on `hae`.  Deriving `hae` by induction over the AE broadcast history is the primary
   remaining gap (target: `AEBroadcastInvariant.lean`, ~10–20 theorems).
2. **`RaftReachable.step` hypotheses are abstract** — They precisely capture what
   preserves `CommitCertInvariant` but do not yet correspond to concrete Raft protocol
   transitions end-to-end. `ConcreteProtocolStep.lean` (CPS2) provides the A5 bridge
   (`ValidAEStep → RaftReachable`), and ECM6 provides `hqc_preserved` conditional on `hae`.
3. **A6 term safety not yet connected to `RaftReachable.step`** — `MaybeCommit.lean`
   (MC4) formally proves A6, and `CommitRule.lean` (CR8) bridges the commit rule to
   `hnew_cert`. Connecting MC4 directly into the `RaftReachable.step` chain remains
   future work.
4. **Panic paths omitted** — `RaftLogAppend.lean` covers the success path of `RaftLog::append`
   only.  The `fatal!()` panic on `ents[0].index - 1 < committed` is not modelled.

These are all documented modelling choices, not semantic errors. No proved theorem is
invalidated by these gaps.

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24697924459) automated formal verification. Run 48: Task 6 Correspondence Review — added RaftLogAppend.lean and ElectionConcreteModel.lean sections (505 theorems, 32 Lean files, 0 sorry).
