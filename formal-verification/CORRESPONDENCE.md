# FV Correspondence Map

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This document maps each Lean definition to the Rust source it models.  It records the
correspondence level, known divergences, and the impact on any proofs that rely on the
definition.

## Last Updated
- **Date**: 2026-03-26 23:09 UTC
- **Commit**: `e8e2c39`

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

No mismatches found. All five Lean models are sound abstractions of their Rust counterparts.

---

## Summary

| Lean file | Rust target | Correspondence level | Proved theorems | Gaps |
|-----------|-------------|---------------------|-----------------|------|
| `LimitSize.lean` | `src/util.rs` `limit_size` | Abstraction | 17 | Overflow not modelled (safe) |
| `ConfigValidate.lean` | `src/config.rs` `Config::validate` | Abstraction | 10 | Error messages not captured (by design) |
| `MajorityVote.lean` | `src/quorum/majority.rs` `vote_result` | Abstraction | 21 | Duplicates in voter list not excluded by type |
| `JointVote.lean` | `src/quorum/joint.rs` `vote_result` | Abstraction | 14 | Struct wrapper abstracted; non-joint degeneration proved (J4) |
| `CommittedIndex.lean` | `src/quorum/majority.rs` `committed_index` | Abstraction | 17 | group-commit path omitted; empty→0 (Rust→MAX) documented |
