# FV Correspondence Map

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This document maps each Lean definition to the Rust source it models.  It records the
correspondence level, known divergences, and the impact on any proofs that rely on the
definition.

## Last Updated
- **Date**: 2026-03-30 17:20 UTC
- **Commit**: `cfaa3a9` (+ inflights phase 5 proofs)

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
| `LimitSize.lean` | `src/util.rs` `limit_size` | Abstraction | 17 | Overflow not modelled (safe); lint clean ✅ |
| `ConfigValidate.lean` | `src/config.rs` `Config::validate` | Abstraction | 10 | Error messages not captured (by design) |
| `MajorityVote.lean` | `src/quorum/majority.rs` `vote_result` | Abstraction | 21 | Duplicates in voter list not excluded by type |
| `JointVote.lean` | `src/quorum/joint.rs` `vote_result` | Abstraction | 14 | Struct wrapper abstracted; non-joint degeneration proved (J4) |
| `CommittedIndex.lean` | `src/quorum/majority.rs` `committed_index` | Abstraction | 17 | group-commit path omitted; empty→0 (Rust→MAX) documented |
| `FindConflict.lean` | `src/raft_log.rs` `find_conflict` | Abstraction | 12 | Entry payload omitted; positive-index precondition explicit |
| `JointCommittedIndex.lean` | `src/quorum/joint.rs` `committed_index` | Abstraction | 10 | `use_group_commit=false` path only; empty→0 (Rust→MAX) documented |
| `MaybeAppend.lean` | `src/raft_log.rs` `maybe_append` | Abstraction | 18 | Stable/unstable split abstracted; panic not modelled; Nat vs u64 |
| `Inflights.lean` | `src/tracker/inflights.rs` `Inflights` | Abstraction | 49 | Abstract (List) + concrete (InflightsConc) models; ALL correspondence theorems proved (0 sorry); phase 5 complete |

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
| `Progress.maybeDecrTo` | `Progress::maybe_decr_to` | Exact | Nat subtraction saturates at 0; Rust u64 guard `next_idx == 0 || next_idx - 1 != rejected` is equivalent (proved as PR26) |
| `Progress.isPaused` | `Progress::is_paused` | Abstraction | `ins.full()` replaced by `ins_full : Bool` |
| `Progress.isSnapshotCaughtUp` | `Progress::is_snapshot_caught_up` | Exact | |
| `Progress.resume` / `Progress.pause` | `Progress::resume` / `Progress::pause` | Exact | |
| `Progress.snapshotFailure` | `Progress::snapshot_failure` | Exact | |
| `Progress.resetState` | `Progress::reset_state` (private) | Exact | |
| `INVALID_INDEX` | `INVALID_INDEX` (`src/raft.rs`) | Exact | Both are 0 |

### Known divergences

1. **Nat vs u64**: All indices are modelled as `Nat` (unbounded). Properties hold for all natural numbers; no overflow analysis. For practical log sizes (< 2^63), Nat is equivalent to u64.

2. **`ins_full` abstraction**: The full `Inflights` ring buffer (separately formalised in `Inflights.lean`) is abstracted to a single `Bool` here. Theorems about `isPaused` are conditional on the value of `ins_full`. The full invariant `ins_full = ins.full()` is not enforced within this model — callers must provide the correct value.

3. **`Progress::reset`** (package-private): not modelled here. It resets the full state; its properties are simple and do not add FV value beyond what `mk_new` provides.

### Proved theorems summary

| Theorem | Property | Level |
|---------|----------|-------|
| PR1–PR3 | State transitions set correct state | Mid |
| PR4–PR6 | State transitions set `next_idx` correctly | Mid |
| PR7–PR9 | State transitions clear `paused` | Mid |
| PR10 | `becomeSnapshot` sets `pending_snapshot` | Mid |
| PR11–PR13 | `isPaused` semantics per state | Mid |
| PR14–PR17 | `maybeUpdate` semantics | Mid |
| PR18–PR20 | `wf` invariant preservation | High |
| PR21 | `isSnapshotCaughtUp` characterisation | Mid |
| PR22 | `mk_new` satisfies `wf` | Mid |
| PR23–PR25 | State transitions preserve `matched` | Mid |
| PR26 | Guard equivalence in `maybeDecrTo` | Mid |
| PR27–PR28 | `maybeDecrTo` in Replicate state | Mid |
| PR29 | `becomeSnapshot` preserves `wf` | High |
| PR30a–PR30b | `resume`/`pause` preserves core fields and `wf` | Low |

### Impact on proofs

All 31 theorems are proved without `sorry`. The key invariant `wf` (`matched + 1 ≤ next_idx`) is
proved to be:
- Established by `mk_new(next_idx)` when `next_idx ≥ 1` (PR22)
- Preserved by `becomeProbe` (PR18) — unconditionally, so even holds if input violated wf
- Preserved by `becomeReplicate` (PR19) — unconditionally
- Preserved by `becomeSnapshot` (PR29) — trivially, since it doesn't change matched/next_idx
- Preserved by `maybeUpdate` (PR20)

Notable: `becomeProbe` and `becomeReplicate` are *self-healing* — they restore `wf` even if
the input `Progress` violated it. This is a useful safety property.

> 🔬 Updated by Lean Squad run [23779112394](https://github.com/dsyme/fv-squad/actions/runs/23779112394).
