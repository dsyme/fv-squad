# Formal Verification Research — `raft-rs`

> 🔬 *Lean Squad — automated formal verification survey for this repository.*

## Repository Overview

`raft-rs` is a Rust implementation of the [Raft distributed consensus algorithm](https://raft.github.io/), forked from and used by [TiKV](https://github.com/tikv/tikv). It implements only the **core Consensus Module**; storage, state machine, and transport are left to consumers.

**Primary language**: Rust  
**Key crates**: `raft` (main), `raft-proto` (protobuf definitions), `harness` (test harness), `datadriven` (data-driven testing)

**Codebase size**: ~8,800 lines in `src/`, with extensive unit and data-driven tests.

## FV Tool Choice

**Tool**: Lean 4 with [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)

**Rationale**:
- Lean 4 provides expressive dependent types suited to modelling Raft's data invariants.
- Mathlib offers rich automation (`omega`, `simp`, `decide`) and relevant libraries (lists, natural number arithmetic, finite sets).
- The project has no existing FV infrastructure in any other tool.
- The purely functional core of many Raft modules (quorum computation, log indexing) maps cleanly to Lean functions.

## Identified FV Targets

### Target 1 — `majority` utility + `MajorityConfig::vote_result` (★★★★★ Priority)

**Files**: `src/util.rs`, `src/quorum/majority.rs`

**What it does**: The `majority(n)` function computes `n/2 + 1`. `MajorityConfig::vote_result` uses it to determine whether a quorum of voters has approved a vote.

**Why FV**: This is the heart of Raft's safety guarantee. Getting quorum calculations wrong breaks the consensus invariant. The logic is simple enough to be fully proved in Lean.

**Key properties to verify**:
1. `majority(n) * 2 > n` — two majorities overlap
2. `majority(n) > 0` for `n > 0`
3. If `yes ≥ majority(n)`, result is `Won`
4. If `yes + missing < majority(n)`, result is `Lost`
5. If `yes < majority(n) ≤ yes + missing`, result is `Pending`
6. Empty voters config → always `Won` (by convention)

**Spec size**: ~40–60 Lean lines  
**Proof tractability**: `omega` and `decide` for arithmetic; `simp`+`cases` for the case analysis. Very tractable.  
**Approximations**: None — the logic is already pure and side-effect-free.

---

### Target 2 — `MajorityConfig::committed_index` (★★★★ Priority)

**File**: `src/quorum/majority.rs`

**What it does**: Given a map from voter IDs to their acknowledged log indices, computes the highest log index that a quorum of voters has acknowledged (i.e., the commit index).

**Why FV**: This is the core "what is committed" computation. An off-by-one error here would allow the leader to commit entries that haven't reached a quorum — a serious safety violation.

**Key properties to verify**:
1. The returned index is ≤ the index reported by at least `majority(n)` voters.
2. If all voters report the same index `i`, the committed index is `i`.
3. For an empty config, returns `u64::MAX` (by convention, plays well with joint quorum).
4. Monotonicity: if every voter's index increases, the committed index can only increase.

**Spec size**: ~80 Lean lines  
**Proof tractability**: Requires reasoning about sorted arrays and medians. Inductive + `omega`. Moderate difficulty.  
**Approximations**: The group-commit extension (multi-datacenter) adds complexity; initial spec can ignore `use_group_commit=true`.

---

### Target 3 — `Unstable` log buffer invariants (★★★ Priority)

**File**: `src/log_unstable.rs`

**What it does**: Maintains a buffer of log entries not yet persisted to stable storage, plus an optional snapshot. Entries are indexed: `entries[i].index == offset + i`.

**Why FV**: The index-offset invariant is critical. Violating it would mean `maybe_term` or `slice` return wrong entries, potentially leading the leader to commit wrong data.

**Key properties to verify**:
1. **Representation invariant**: if entries is non-empty, `entries[i].index == offset + i` for all `i`.
2. `maybe_last_index` returns `offset + entries.len() - 1` when entries is non-empty.
3. `maybe_term(idx)` returns `Some(t)` iff `idx` is in range.
4. `truncate_and_append` preserves the representation invariant.
5. After `stable_entries(index, term)`, `entries` is empty and `offset` advances correctly.

**Spec size**: ~120 Lean lines  
**Proof tractability**: Structural induction on list operations; moderate difficulty.  
**Approximations**: Must abstract away `Logger` (I/O); model entries as `(index: Nat, term: Nat)` pairs.

---

### Target 4 — `Inflights` ring buffer (★★★ Priority)

**File**: `src/tracker/inflights.rs`

**What it does**: A circular buffer tracking in-flight (sent but unacknowledged) log indices for each peer. Used for flow control.

**Why FV**: Ring buffer off-by-one errors are a classic source of bugs. The `add`/`free_to` operations must maintain the circular buffer invariant.

**Key properties to verify**:
1. **Capacity invariant**: `count ≤ cap` always holds.
2. **Content preservation**: after `add(x)`, `x` is in the logical window.
3. After `free_to(k)`, all entries `≤ k` are removed from the window.
4. `free_first_one` is equivalent to `free_to(buffer[start])`.
5. `reset` yields an empty, valid buffer.

**Spec size**: ~100 Lean lines  
**Proof tractability**: The wrapping arithmetic requires careful `omega`/`norm_num`. Moderate difficulty.  
**Approximations**: Model buffer as a list with phantom `start` index; abstract away `Vec` resizing.

---

### Target 5 — `limit_size` utility (★★ Priority)

**File**: `src/util.rs`

**What it does**: Truncates a list of entries so their total byte size does not exceed a given limit, but always keeps at least one entry.

**Key properties to verify**:
1. Result always has `len ≥ 1` (at least one entry preserved).
2. If `max = NO_LIMIT`, entries are unchanged.
3. Sum of sizes of retained entries ≤ `max` (when `len ≥ 2`).
4. First entry is always retained.

**Spec size**: ~50 Lean lines  
**Proof tractability**: Easy — `omega` + list reasoning. Good warmup.  
**Approximations**: Abstract away protobuf `compute_size`; model entry size as a natural number.

---

### Target 6 — `Progress` Replication State Machine (★★★★ Priority)

**Files**: `src/tracker/progress.rs`, `src/tracker/state.rs`

**What it does**: `Progress` is the Raft leader's per-follower view of the
replication pipeline. It is a three-state machine (Probe/Replicate/Snapshot)
with two key fields: `matched` (highest acknowledged log index) and `next_idx`
(next index to send). State transitions and the `maybe_update`/`maybe_decr_to`
operations update these fields with strict ordering constraints.

**Why FV**: The core invariant `matched + 1 ≤ next_idx` is critical for Raft
safety — violating it would cause the leader to send entries with incorrect
indices, breaking log consistency. The state transition logic (especially
`become_probe` from Snapshot state) has subtle max-of-two-bounds reasoning that
is easy to get wrong.

**Key properties to verify**:
1. **INV-1 (index ordering)**: `matched + 1 ≤ next_idx` — always holds.
2. `maybe_update(n)` sets `matched = max(old.matched, n)` and
   `next_idx = max(old.next_idx, n+1)`.
3. `maybe_update` returns `true` iff `n > old.matched`.
4. `become_probe` from Snapshot state sets `next_idx = max(matched+1, pending_snapshot+1)`.
5. All state transitions preserve INV-1.
6. `maybe_decr_to` in Replicate state never moves `next_idx` below `matched+1`.
7. `maybe_update` is monotone: if `n₁ ≤ n₂`, updating with `n₂` after `n₁`
   gives the same `matched` as updating directly with `n₂`.

**Spec size**: ~120 Lean lines (types + theorems)
**Proof tractability**: `omega` handles all arithmetic; `simp` + `cases` for
state discrimination. Very tractable — no induction required.
**Approximations**:
- `Inflights` (in-flight message tracker) omitted from model; `is_paused` in
  Replicate state approximated as always `false`.
- `committed_index` and `pending_request_snapshot` fields omitted.
- `u64` modelled as `Nat`.

## Mathlib Modules of Interest

- `Mathlib.Data.List.Basic` — list lemmas for `truncate_and_append`
- `Mathlib.Data.Finset.Basic` — finite sets for voter configurations
- `Mathlib.Data.Finset.Card` — cardinality for quorum proofs
- `Mathlib.Order.Defs` — ordering for commit index monotonicity
- `Mathlib.Algebra.Order.Ring.Lemmas` — arithmetic for `majority`
- `Mathlib.Data.Nat.Defs` — natural number arithmetic

## General Approach

1. Model Raft concepts as simple Lean inductive types (ignoring protobuf, I/O, logging).
2. State correctness properties as `theorem` declarations.
3. Use `decide` for small finite cases; `omega` for arithmetic; induction for structural properties.
4. Explicitly document what the model does NOT capture (networking, storage I/O, failure modes).
5. Leave `sorry` as a placeholder for hard sub-goals; prefer partial proofs over no proofs.

## Web References Consulted

- [Raft paper](https://raft.github.io/raft.pdf) — original algorithm specification
- [Mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/) — available lemmas
- etcd Raft Go implementation (referenced in source comments) for design intent
