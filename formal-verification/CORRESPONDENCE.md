# Lean ↔ Rust Correspondence

This document maps every Lean 4 file in `formal-verification/lean/FVSquad/` to the
Rust source it models, explains the correspondence in detail, and records known
approximations and divergences.

Each Lean file's module-level doc-comment also contains a "Model scope and
approximations" section; this document is the single authoritative cross-reference.

---

## Summary table

| Lean file | Rust file(s) | Key Rust items | Status |
|-----------|-------------|----------------|--------|
| [`MajorityQuorum.lean`](#majorityquorum) | `src/util.rs`, `src/quorum/majority.rs` | `majority()`, `Configuration::vote_result()` | ✅ Fully proved |
| [`CommittedIndex.lean`](#committedindex) | `src/quorum/majority.rs` | `Configuration::committed_index()` | ✅ Fully proved |
| [`UnstableLog.lean`](#unstablelog) | `src/log_unstable.rs` | `Unstable` struct + all methods | ✅ Fully proved |
| [`Inflights.lean`](#inflights) | `src/tracker/inflights.rs` | `Inflights` struct + all methods | ✅ Fully proved |
| [`LimitSize.lean`](#limitsize) | `src/util.rs` | `limit_size()` | ✅ Fully proved |
| [`Progress.lean`](#progress) | `src/tracker/progress.rs`, `src/tracker/state.rs` | `Progress` struct, state machine ops | ✅ Fully proved |
| [`JointQuorum.lean`](#jointquorum) | `src/quorum/joint.rs` | `JointConfig::vote_result()`, `JointConfig::committed_index()` | ✅ Fully proved |
| [`LogOrdering.lean`](#logordering) | `src/raft_log.rs` | `RaftLog::is_up_to_date()`, `RaftLog::find_conflict_by_term()` | ✅ Fully proved |
| [`MaybeAppend.lean`](#maybeappend) | `src/raft_log.rs` | `RaftLog::maybe_append()` | ✅ Fully proved |
| [`MaybeCommit.lean`](#maybecommit) | `src/raft_log.rs` | `RaftLog::maybe_commit()` | ✅ Fully proved |
| [`MaybePersist.lean`](#maybepersist) | `src/raft_log.rs` | `RaftLog::maybe_persist()` | ✅ Fully proved |
| [`ProgressTracking.lean`](#progresstracking) | `src/tracker/progress.rs` | `maybe_update()`, `update_committed()`, `maybe_decr_to()` | ✅ Fully proved |
| [`ReadOnly.lean`](#readonly) | `src/read_only.rs` | `ReadOnly` struct + `add_request()`, `recv_ack()`, `advance()` | ✅ Fully proved |
| [`QuorumRecentlyActive.lean`](#quorumrecentlyactive) | `src/tracker.rs` | `ProgressTracker::quorum_recently_active()` | ✅ Fully proved |
| [`NextEntries.lean`](#nextentries) | `src/raft_log.rs` | `RaftLog::next_entries_since()`, `applied_index_upper_bound()` | 🔄 In progress |

---

## MajorityQuorum

**Lean file**: [`lean/FVSquad/MajorityQuorum.lean`](lean/FVSquad/MajorityQuorum.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `majority` | [`src/util.rs:117`](../src/util.rs#L117) | `pub fn majority(total: usize) -> usize` |
| `VoteResult` | [`src/quorum/majority.rs:3`](../src/quorum/majority.rs#L3) (via `use super::VoteResult`) | enum in `src/quorum/mod.rs` |
| `voteResult` | [`src/quorum/majority.rs:130`](../src/quorum/majority.rs#L130) | `pub fn vote_result(&self, check: impl Fn(u64) -> Option<bool>) -> VoteResult` |

### Correspondence

**`majority(n)`** — The Rust function is:
```rust
// src/util.rs:117
pub fn majority(total: usize) -> usize {
    (total / 2) + 1
}
```
The Lean model is `def majority (n : Nat) : Nat := n / 2 + 1` — an exact translation.
Both use integer (floor) division. The only difference is that Rust uses `usize`
(bounded machine integer), while Lean uses `Nat` (unbounded); no property proved here
depends on overflow behaviour.

**`VoteResult`** — The Rust enum is defined in `src/quorum/mod.rs` and re-exported.
The Lean `inductive VoteResult` with constructors `Pending | Lost | Won` mirrors it
exactly, with the same three variants and the same semantics.

**`vote_result`** — The Rust code iterates over `self.voters` (a `HashSet<u64>`) and
calls `check(v)` for each voter, yielding `Some(true)` (yes), `Some(false)` (no), or
`None` (not yet voted). The Lean model lifts this to:
- `voters : Finset Nat` — models `HashSet<u64>` without hash-map internals
- `VoteAssignment := Nat → Option Bool` — models `check: impl Fn(u64) -> Option<bool>`
- `yesCount` / `missingCount` — count yes and pending votes over the finset

The case logic in Lean's `voteResult` matches the Rust `match` exactly:
- `yes ≥ q` → `Won`
- `yes + missing ≥ q` → `Pending`
- otherwise → `Lost`

### Approximations / divergences

- Voter IDs are `Nat` instead of `u64`; 64-bit overflow is not modelled (not relevant to quorum algebra).
- `HashSet` is modelled as `Finset` (no hash-map implementation details).

---

## CommittedIndex

**Lean file**: [`lean/FVSquad/CommittedIndex.lean`](lean/FVSquad/CommittedIndex.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `committedIndex` | [`src/quorum/majority.rs:70`](../src/quorum/majority.rs#L70) | `pub fn committed_index(&self, use_group_commit: bool, l: &impl AckedIndexer) -> (u64, bool)` |
| `AckedFn` | [`src/quorum/majority.rs:70`](../src/quorum/majority.rs#L70) | `impl AckedIndexer` (trait) |
| `sortDesc` | [`src/quorum/majority.rs:85`](../src/quorum/majority.rs#L85) | `matched.sort_by(|a, b| b.index.cmp(&a.index))` |
| `countGe` | (derived; no direct Rust counterpart) | Declarative characterisation only |

### Correspondence

The Rust algorithm (non-group-commit path, lines 70–123):
1. Collect `l.acked_index(v).unwrap_or_default()` for every voter.
2. Sort the collected values in **descending** order (`sort_by |a, b| b.index.cmp(&a.index)`).
3. Return `sorted[majority(n) - 1]`.

The Lean model reproduces this faithfully:
- `AckedFn := Nat → Nat` models `impl AckedIndexer` with `None ↦ 0` (same as `unwrap_or_default()`).
- `sortDesc` uses `List.mergeSort (· ≥ ·)`, matching the Rust reverse sort.
- `committedIndex` picks element at `majority(voters.card) - 1` — same index as Rust's `quorum - 1`.

The Rust uses a small stack array (`[MaybeUninit<Index>; 7]`) for up to 7 voters and a
heap `Vec` for larger sets. This is a performance optimisation only; the Lean model uses
`List` throughout, which is semantically equivalent.

**Key theorems and their Rust meaning**:
- `committedIndex_safety`: the returned index has been acked by ≥ majority(n) voters — the core Raft safety invariant for commit.
- `committedIndex_maximal`: no larger index has quorum support — the returned value is the *maximum* such index.
- `committedIndex_monotone`: if acked indices only grow, the committed index can only grow ("Raft never uncommits").

### Approximations / divergences

- **Group-commit path not modelled**: when `use_group_commit = true` the Rust adds cross-group criteria. This is explicitly documented in the file and deferred.
- **Empty config returns `0` not `u64::MAX`**: Rust returns `u64::MAX` as a sentinel for joint quorums. The Lean model returns `0` (staying in `Nat`) and documents this divergence in `committedIndex_empty_contract`.

---

## UnstableLog

**Lean file**: [`lean/FVSquad/UnstableLog.lean`](lean/FVSquad/UnstableLog.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `Unstable` (struct) | [`src/log_unstable.rs:27`](../src/log_unstable.rs#L27) | `pub struct Unstable { snapshot, entries, entries_size, offset, logger }` |
| `maybeFirstIndex` | [`src/log_unstable.rs:62`](../src/log_unstable.rs#L62) | `pub fn maybe_first_index(&self) -> Option<u64>` |
| `maybeLastIndex` | [`src/log_unstable.rs:69`](../src/log_unstable.rs#L69) | `pub fn maybe_last_index(&self) -> Option<u64>` |
| `maybeTerm` | [`src/log_unstable.rs:77`](../src/log_unstable.rs#L77) | `pub fn maybe_term(&self, idx: u64) -> Option<u64>` |
| `stableEntries` | [`src/log_unstable.rs:98`](../src/log_unstable.rs#L98) | `pub fn stable_entries(&mut self, index: u64, term: u64)` |
| `stableSnap` | [`src/log_unstable.rs:126`](../src/log_unstable.rs#L126) | `pub fn stable_snap(&mut self, index: u64)` |
| `restore` | [`src/log_unstable.rs:147`](../src/log_unstable.rs#L147) | `pub fn restore(&mut self, snap: Snapshot)` |
| `truncateAndAppend` | [`src/log_unstable.rs:159`](../src/log_unstable.rs#L159) | `pub fn truncate_and_append(&mut self, ents: &[Entry])` |

### Correspondence

The central invariant is the **representation invariant** (`wellFormed`):
```
entries[i].index == offset + i   for all i < entries.len()
```
This is modelled in Lean as:
```lean
def wellFormed (u : Unstable) : Prop :=
  ∀ i, i < u.entries.length →
    (u.entries.get ⟨i, ...⟩).index = u.offset + i
```
which corresponds to the implicit invariant maintained throughout `log_unstable.rs`.

Each operation's Lean model closely tracks the Rust:
- `maybeLastIndex`: Lean `match entries.length with | 0 => snapshot.map ... | n => some (offset + n - 1)` mirrors the Rust `match self.entries.len()` exactly.
- `truncateAndAppend`: Lean truncates entries to those before the new entries' first index, then appends — matching Rust's `self.entries.truncate(...)` + `self.entries.extend(...)`.
- `stableEntries`: Lean sets `offset := entries.last.index + 1` and clears `entries` — matching Rust's `self.offset = entry.get_index() + 1; self.entries.clear()`.

### Approximations / divergences

- `entries_size` field (byte-size cache) is omitted — it is a performance cache derivable from entries.
- `Logger` is omitted — I/O side effects are not modelled.
- `fatal!` panics are replaced with preconditions.
- Log entries are modelled as `(index: Nat, term: Nat)` pairs (abstracting away payload bytes).

---

## Inflights

**Lean file**: [`lean/FVSquad/Inflights.lean`](lean/FVSquad/Inflights.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `Inflights` (struct) | [`src/tracker/inflights.rs:1`](../src/tracker/inflights.rs#L1) | `pub struct Inflights { cap, start, count, buffer }` |
| `full` | [`src/tracker/inflights.rs:87`](../src/tracker/inflights.rs#L87) | `pub fn full(&self) -> bool` |
| `add` | [`src/tracker/inflights.rs:92`](../src/tracker/inflights.rs#L92) | `pub fn add(&mut self, inflight: u64)` |
| `freeTo` | [`src/tracker/inflights.rs:118`](../src/tracker/inflights.rs#L118) | `pub fn free_to(&mut self, to: u64)` |
| `freeFirstOne` | [`src/tracker/inflights.rs:156`](../src/tracker/inflights.rs#L156) | `pub fn free_first_one(&mut self)` |
| `reset` | [`src/tracker/inflights.rs:165`](../src/tracker/inflights.rs#L165) | `pub fn reset(&mut self)` |

### Correspondence

The Rust `Inflights` is a circular/ring buffer with fields `start`, `count`, `cap`, and
`buffer: Vec<u64>`. The ring buffer semantics mean that `add` writes to
`buffer[(start + count) % cap]` and `free_to` advances `start`.

The Lean model **abstracts the ring buffer** to a plain `List Nat` (`items`) giving the
logical queue contents in FIFO order. This abstraction is sound: all observable
behaviour (which indices are in flight, whether the buffer is full) is captured by the
logical list.

The `concrete` model in the Lean file also contains a ring-buffer model closer to the
Rust implementation, and `concreteAdd_abstract` / `concreteFreeTo_abstract` lemmas prove
that the concrete model refines the abstract model.

**`free_to` semantics**: Rust frees all entries whose index ≤ `to` from the front of the
queue. Lean models this as `List.dropWhile (· ≤ to)` — equivalent when the queue is
monotone (INV-4), which holds in correct Raft usage.

### Approximations / divergences

- Ring-buffer layout (`start`, `buffer`) is abstracted to `List Nat` in the primary model.
- `incoming_cap` / `set_cap` (capacity adjustment) is deferred.
- INV-4 (strictly increasing indices) is stated as a predicate but not enforced by the model.

---

## LimitSize

**Lean file**: [`lean/FVSquad/LimitSize.lean`](lean/FVSquad/LimitSize.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `limitSize` | [`src/util.rs:51`](../src/util.rs#L51) | `pub fn limit_size<T: PbMessage + Clone>(entries: &mut Vec<T>, max: Option<u64>)` |
| `limitSizeGo` | [`src/util.rs:60`](../src/util.rs#L60) | inner `take_while` closure |

### Correspondence

The Rust function uses an iterator with `take_while`:
```rust
let mut size = 0u64;
let limit = entries.iter().take_while(|&e| {
    if size == 0 { size += e.compute_size(); return true }
    size += e.compute_size();
    size <= max
}).count();
entries.truncate(limit);
```

The Lean model introduces `limitSizeGo lim acc count entries` which scans the list
accumulating `acc` (running byte total) and `count` (accepted entries), accepting entry
`x` iff `acc = 0 ∨ acc + x ≤ lim`. This exactly captures the `size == 0` branch
(first entry always accepted) and the `size <= max` branch.

Each entry's size is abstracted to a single `Nat` (the `compute_size()` value). The
`limitSize` function then wraps `limitSizeGo` to produce the truncated list.

**Key theorems**:
- `limitSize_is_prefix`: result is a prefix of the input (Rust: `truncate`).
- `limitSize_length_ge_one`: at least one entry kept for non-empty input (Rust: `if entries.len() <= 1 { return }`).
- `limitSize_sum_le`: total byte size ≤ limit when > 1 entry kept (the budget safety property).
- `limitSize_maximal`: adding the next entry would exceed the limit (correctness of the stopping criterion).

### Approximations / divergences

- `NO_LIMIT` (`u64::MAX`) sentinel is not modelled; `None` is used directly.
- `u64` overflow of the `size` accumulator is not modelled (Lean uses `Nat`).
- Entry payloads are abstracted to a single `Nat` size value.

---

## Progress

**Lean file**: [`lean/FVSquad/Progress.lean`](lean/FVSquad/Progress.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `ProgressState` | [`src/tracker/state.rs`](../src/tracker/state.rs) | `pub enum ProgressState { Probe, Replicate, Snapshot }` |
| `Progress` (struct) | [`src/tracker/progress.rs:11`](../src/tracker/progress.rs#L11) | `pub struct Progress { matched, next_idx, state, paused, pending_snapshot, ... }` |
| `becomeProbe` | [`src/tracker/progress.rs:94`](../src/tracker/progress.rs#L94) | `pub fn become_probe(&mut self)` |
| `becomeReplicate` | [`src/tracker/progress.rs:110`](../src/tracker/progress.rs#L110) | `pub fn become_replicate(&mut self)` |
| `becomeSnapshot` | [`src/tracker/progress.rs:117`](../src/tracker/progress.rs#L117) | `pub fn become_snapshot(&mut self, snapshot_idx: u64)` |
| `maybeUpdate` | [`src/tracker/progress.rs:136`](../src/tracker/progress.rs#L136) | `pub fn maybe_update(&mut self, n: u64) -> bool` |
| `optimisticUpdate` | [`src/tracker/progress.rs:159`](../src/tracker/progress.rs#L159) | `pub fn optimistic_update(&mut self, n: u64)` |

### Correspondence

The Lean `Progress` struct closely mirrors the Rust `Progress` struct. The Rust struct
has additional fields (`ins: Inflights`, `commit_group_id`, `pending_request_snapshot`)
that are either omitted or present but not constrained in this module (they are covered
in `ProgressTracking.lean`).

The core **representation invariant** (`valid`) is `matched + 1 ≤ next_idx` — the next
index to send is strictly beyond the last acknowledged index. This corresponds to the
implicit invariant throughout `progress.rs`.

Each state-transition method maps one-to-one:
- **`become_probe`**: The Rust special-cases the Snapshot state (setting `next_idx` from
  `pending_snapshot + 1`). The Lean `becomeProbe` uses the same `match p.state` logic.
- **`become_replicate`**: Both set `next_idx := matched + 1`.
- **`become_snapshot`**: Both set `pending_snapshot := snapIdx` and clear state.
- **`maybe_update(n)`**: Both advance `matched` and `next_idx` when `n > matched`.
- **`optimistic_update(n)`**: Both set `next_idx := n + 1`.

The master invariant theorem `valid_preserved_by_all_ops` proves that all operations
preserve `matched + 1 ≤ next_idx` — the key soundness result.

### Approximations / divergences

- `ins: Inflights` is omitted (modelled separately in `Inflights.lean`).
- `is_paused` in Replicate state is approximated as always `false`.
- `pending_request_snapshot` and `commit_group_id` are omitted.

---

## JointQuorum

**Lean file**: [`lean/FVSquad/JointQuorum.lean`](lean/FVSquad/JointQuorum.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `JointConfig` | [`src/quorum/joint.rs:1`](../src/quorum/joint.rs#L1) | `pub struct JointConfig([Configuration; 2])` |
| `jointVoteResult` | [`src/quorum/joint.rs:56`](../src/quorum/joint.rs#L56) | `pub fn vote_result(&self, check: impl Fn(u64) -> Option<bool>) -> VoteResult` |
| `jointCommittedIndex` | [`src/quorum/joint.rs:47`](../src/quorum/joint.rs#L47) | `pub fn committed_index(&self, use_group_commit: bool, l: &impl AckedIndexer) -> (u64, bool)` |

### Correspondence

**Joint vote result**: The Rust iterates over the two `Configuration`s and combines their
individual `vote_result` outcomes:
- `Won` only if both configs vote Won.
- `Lost` if either config votes Lost.
- `Pending` otherwise.

Lean's `jointVoteResult` uses the same case structure, composing
`FVSquad.MajorityQuorum.voteResult` for each half.

**Joint committed index**: The Rust returns `cmp::min(i_idx, o_idx)` — the minimum of
the two individual committed indices. Lean's `jointCommittedIndex i_idx o_idx := min i_idx o_idx`
is an exact translation.

The `JointConfig` in Rust is `[Configuration; 2]` (an array of two majority configs).
Lean models this as `{ incoming : Finset Nat, outgoing : Finset Nat }`, which captures
the same two-config structure.

### Approximations / divergences

- `use_group_commit` flag and the group-commit algorithm are not modelled.
- The empty-config sentinel (`u64::MAX`) divergence is inherited from `CommittedIndex.lean`.

---

## LogOrdering

**Lean file**: [`lean/FVSquad/LogOrdering.lean`](lean/FVSquad/LogOrdering.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `isUpToDate` | [`src/raft_log.rs:437`](../src/raft_log.rs#L437) | `pub fn is_up_to_date(&self, last_index: u64, term: u64) -> bool` |
| `findConflictByTerm` | [`src/raft_log.rs:222`](../src/raft_log.rs#L222) | `pub fn find_conflict_by_term(&self, index: u64, term: u64) -> (u64, Option<u64>)` |

### Correspondence

**`is_up_to_date`**: In Raft, a candidate's log is "up to date" if its last log term is
greater than the local last term, or if terms are equal and its last log index is ≥ the
local last index. The Rust:
```rust
pub fn is_up_to_date(&self, last_index: u64, term: u64) -> bool {
    term > self.last_term() || (term == self.last_term() && last_index >= self.last_index())
}
```
The Lean `isUpToDate` encodes the same lexicographic order on `(term, index)` pairs.
The proofs establish this is a total preorder, which is exactly the ordering Raft §5.4.1
requires for leader election safety.

**`find_conflict_by_term`**: The Rust scans backwards from `index` to find the highest
index `i ≤ index` such that `self.term(i) ≤ term`. The Lean `findConflictByTerm`
models this as a functional scan and proves the maximality property: the returned index
is the greatest index with term ≤ the given term.

### Approximations / divergences

- Log entries are modelled as an abstract `logTerm : Nat → Option Nat` function (opaque term map).
- `last_term()` and `last_index()` are passed as parameters rather than computed from state.

---

## MaybeAppend

**Lean file**: [`lean/FVSquad/MaybeAppend.lean`](lean/FVSquad/MaybeAppend.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `maybeAppend` | [`src/raft_log.rs:262`](../src/raft_log.rs#L262) | `pub fn maybe_append(&mut self, idx: u64, term: u64, committed: u64, ents: &[Entry]) -> Option<u64>` |
| `findConflict` | [`src/raft_log.rs:302`](../src/raft_log.rs#L302) | `fn find_conflict(&self, ents: &[Entry]) -> u64` (private) |
| `commitTo` | [`src/raft_log.rs:254`](../src/raft_log.rs#L254) | `pub fn commit_to(&mut self, to_commit: u64)` |

### Correspondence

`maybe_append(idx, term, committed, ents)` checks whether the log entry at `idx` has
the given `term` (using `match_term`). If so, it finds the first conflicting entry among
`ents` (using `find_conflict`), truncates the log there and appends the new entries, then
advances `committed`.

The Lean model:
- `matchTerm s idx term` — models `self.match_term(idx, term)`.
- `findConflict s ents` — models `find_conflict` (scan for first index where the log term differs).
- `maybeAppend s idx term committed ents` — models the full `maybe_append` flow.
- `commitTo s k` — models `commit_to`: advances `committed` monotonically (never decreases).

**Key theorems**:
- `commitTo_monotone`: `committed` never decreases — core Raft safety.
- `maybeAppend_commit_le_leader`: the new committed index is ≤ the leader's `committed` argument.
- `maybeAppend_commit_le_lastNew`: the new committed index is ≤ the last new entry index.

### Approximations / divergences

- Entry payloads are abstracted to `(index, term)` pairs.
- Panic semantics (`commit_to`'s out-of-range check) are modelled as preconditions.
- Applied/persisted indices and snapshot interaction are omitted.

---

## MaybeCommit

**Lean file**: [`lean/FVSquad/MaybeCommit.lean`](lean/FVSquad/MaybeCommit.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `maybeCommit` | [`src/raft_log.rs:525`](../src/raft_log.rs#L525) | `pub fn maybe_commit(&mut self, max_index: u64, term: u64) -> bool` |

### Correspondence

The Rust:
```rust
pub fn maybe_commit(&mut self, max_index: u64, term: u64) -> bool {
    if max_index > self.committed && self.term(max_index).map_or(false, |t| t == term) {
        self.commit_to(max_index);
        true
    } else {
        false
    }
}
```

The Lean `maybeCommit state maxIndex term` applies the same two-part guard:
1. `maxIndex > state.committed`
2. `state.termFn maxIndex = some term`

Both must hold for `committed` to advance. `termFn` models `self.term(max_index)` as a
pure function returning `Option Nat`.

The "term-lock" safety gate (guard 2) corresponds to Raft §5.4.2: a leader may only
directly commit entries from its current term; older entries commit transitively.

**Key theorems**:
- `maybeCommit_guard_iff`: exact characterisation of when the result is `true`.
- `maybeCommit_monotone`: `committed` only increases.
- `maybeCommit_WF`: well-formedness is preserved.
- `maybeCommit_idempotent`: applying twice with the same arguments has no additional effect.

### Approximations / divergences

- `self.term(max_index)` is modelled as `termFn : Nat → Option Nat` (pure, opaque).
- Applied, persisted, and snapshot fields are omitted.

---

## MaybePersist

**Lean file**: [`lean/FVSquad/MaybePersist.lean`](lean/FVSquad/MaybePersist.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `maybePersist` | [`src/raft_log.rs:540`](../src/raft_log.rs#L540) | `pub fn maybe_persist(&mut self, index: u64, term: u64) -> bool` |

### Correspondence

The Rust:
```rust
pub fn maybe_persist(&mut self, index: u64, term: u64) -> bool {
    if index > self.persisted {
        // Check the entry at `index` has the given term, then advance persisted
        ...
        self.unstable.stable_entries(index, term);
        self.persisted = index;
        true
    } else {
        false
    }
}
```

The Lean model captures the guard (`index > persisted`), the term check
(`storedTerm index = some term`), and the monotone advance of `persisted`.

**Key theorems**: WF-preservation, monotonicity of `persisted`, idempotency, and the
fixed-point property (`maybePersist` applied twice to the same index has no further
effect).

### Approximations / divergences

- Interaction with `unstable.stable_entries` is abstracted (modelled as advancing `persisted`).
- `maybe_persist_snap` (snapshot variant) is a separate Rust function, not covered here.

---

## ProgressTracking

**Lean file**: [`lean/FVSquad/ProgressTracking.lean`](lean/FVSquad/ProgressTracking.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `maybeUpdate` | [`src/tracker/progress.rs:136`](../src/tracker/progress.rs#L136) | `pub fn maybe_update(&mut self, n: u64) -> bool` |
| `updateCommitted` | [`src/tracker/progress.rs:151`](../src/tracker/progress.rs#L151) | `pub fn update_committed(&mut self, committed_index: u64)` |
| `maybeDecrTo` | [`src/tracker/progress.rs:166`](../src/tracker/progress.rs#L166) | `pub fn maybe_decr_to(&mut self, rejected: u64, match_hint: u64, request_snapshot: u64) -> bool` |

### Correspondence

This module focuses on three methods that are the leader's primary mechanisms for
updating its per-follower replication view:

**`maybe_update(n)`**: Rust advances `matched` and clears `paused` when `n > matched`,
and ensures `next_idx ≥ n + 1`. The Lean model has the same two-branch structure
(`if p.matched < n` / else).

**`update_committed(ci)`**: Rust advances `committed_index` monotonically
(`if ci > self.committed_index { self.committed_index = ci }`). Lean's `updateCommitted`
has the same guard.

**`maybe_decr_to(rejected, match_hint, request_snapshot)`**: This is the rejection
handler. Rust resets `next_idx` downward when a follower rejects an `AppendEntries`:
- In `Replicate` state: `next_idx := min(rejected, matched + 1)`.
- In `Probe` state: `next_idx := max(rejected - 1, match_hint + 1)` (or similar), then resume.
- In `Snapshot` state: clear `pending_snapshot`.

The Lean `maybeDecrTo` models all three branches.

**Key theorems**: 31 theorems including WF-preservation for all operations (WF =
`next_idx ≥ matched + 1`), stale-rejection characterisation, cross-operation
commutativity.

### Approximations / divergences

- `Inflights.reset()` side effect in `maybe_decr_to` (Replicate state) is omitted.
- `pending_request_snapshot` handling in `maybe_decr_to` is simplified.

---

## ReadOnly

**Lean file**: [`lean/FVSquad/ReadOnly.lean`](lean/FVSquad/ReadOnly.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `ReadOnly` (struct) | [`src/read_only.rs:1`](../src/read_only.rs#L1) | `pub struct ReadOnly { option, pending_read_index, read_index_queue }` |
| `addRequest` | [`src/read_only.rs:82`](../src/read_only.rs#L82) | `pub fn add_request(&mut self, index: u64, req: Message, self_id: u64)` |
| `recvAck` | [`src/read_only.rs:100`](../src/read_only.rs#L100) | `pub fn recv_ack(&mut self, id: u64, ctx: &[u8]) -> Option<&HashSet<u64>>` |
| `advance` | [`src/read_only.rs:110`](../src/read_only.rs#L110) | `pub fn advance(&mut self, ctx: &[u8], logger: &Logger) -> Vec<ReadIndexStatus>` |

### Correspondence

The Rust `ReadOnly` struct implements the ReadIndex protocol's server-side queue:
- `add_request`: enqueues a read request with its context (hash), noting which peers have
  acked. The self-ID is immediately counted as an ack.
- `recv_ack`: records that peer `id` has acked the request for context `ctx`; returns
  the ack set if the context exists.
- `advance`: drains all requests in FIFO order up to and including `ctx`, returning
  their status records for application.

The Lean model represents the queue as a `List ReadIndexStatus` (FIFO order, oldest
first) and an `acksMap : Nat → Finset Nat` (context → ack set). This abstracts the
`HashMap` implementation but captures all behavioural properties.

**Key theorems** (30 total):
- `addRequest_idempotent`: adding the same request twice has no effect on the second call.
- `recvAck_ack_accumulation`: each `recv_ack` only adds to the ack set, never removes.
- `advance_FIFO_drain`: `advance(ctx)` drains exactly the prefix up to and including `ctx`.

### Approximations / divergences

- `ReadIndexOption` (Safe vs LeaseBased) affects only liveness, not safety; modelled as
  a parameter with no effect on queue behaviour.
- `HashMap` context → status map is abstracted to a functional map.
- Logger and I/O are omitted.

---

## QuorumRecentlyActive

**Lean file**: [`lean/FVSquad/QuorumRecentlyActive.lean`](lean/FVSquad/QuorumRecentlyActive.lean)

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `quorumRecentlyActive` | [`src/tracker.rs:336`](../src/tracker.rs#L336) | `pub fn quorum_recently_active(&mut self, perspective_of: u64) -> bool` |

### Correspondence

The Rust iterates over all voter progress records, counting those where
`progress.recent_active = true` (plus the leader itself via `perspective_of`). It
returns `true` iff this count ≥ `majority(voters.len())`.

The Lean model:
- Takes a `voters : Finset Nat` and `activeSet : Finset Nat` (those recently active).
- Adds `perspectiveOf` to `activeSet` unconditionally (self-inclusion).
- Returns `true` iff `(activeSet ∩ voters).card ≥ majority voters.card`.

**Key theorems**: self-inclusion, monotonicity (larger active set → same or higher
result), post-state reset (after the call, `recent_active` flags are cleared for
non-perspective-of voters).

### Approximations / divergences

- The Rust iterates over `progress_map` (a HashMap); the Lean abstracts this to
  `voters : Finset Nat` and `activeSet : Finset Nat`.
- The mutation (`recent_active := false` after checking) is modelled as a separate
  `resetActive` operation.

---

## NextEntries

**Lean file**: [`lean/FVSquad/NextEntries.lean`](lean/FVSquad/NextEntries.lean)

**Status**: 🔄 In progress

### Rust source

| Lean definition | Rust location | Rust signature |
|-----------------|---------------|----------------|
| `nextEntriesSince` | [`src/raft_log.rs:442`](../src/raft_log.rs#L442) | `pub fn next_entries_since(&self, since_idx: u64, max_size: Option<u64>) -> Option<Vec<Entry>>` |
| `appliedIndexUpperBound` | [`src/raft_log.rs:437`](../src/raft_log.rs#L437) | (derived from `is_up_to_date` context) |

### Correspondence

`next_entries_since(since_idx, max_size)` returns the window of committed-but-not-yet-
applied entries: those with index in `(since_idx, committed]`, subject to `max_size`
(via `limit_size`). The Lean model captures the window computation and the
`applied_index_upper_bound` bounding invariant.

This module is still in progress; the remaining `sorry`s cover edge cases in the
interaction between the window bounds and `limit_size`.

### Approximations / divergences

- Entry payloads abstracted to `(index, term)` pairs.
- `limit_size` interaction is partially modelled (pending full integration with
  `LimitSize.lean`).

---

## How to read the correspondence

For each Lean module, the full list of approximations is recorded in the module-level
`/-! ... -/` doc-comment under "Model scope and approximations". This document provides
the cross-reference back to Rust line numbers; the Lean files provide the detailed
justification for each modelling choice.

The intended workflow for verifying that a Lean model is faithful to the Rust:
1. Read the Rust function at the linked line.
2. Read the Lean model definition (same name, camelCase).
3. Check the "Correspondence" section above for a side-by-side explanation.
4. Run the `#eval` sanity checks in the Lean file against the Rust doctests.
5. Consult the "Approximations / divergences" section for any known gaps.
