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

**File**: `src/tracker/inflights.rs` — Ring buffer invariants. Medium tractability.

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
