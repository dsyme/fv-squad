# Informal Specification: `RaftLog::append`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Target**: `RaftLog::append` in `src/raft_log.rs` (line 382)  
**Phase**: 2 — Informal Specification  
**Related Lean files**: `FVSquad/LogUnstable.lean` (models `truncate_and_append`)  
**Related informal specs**: `log_unstable_informal.md`, `maybe_append_informal.md`

---

## Purpose

`RaftLog::append(ents)` writes a (possibly conflicting) batch of entries into the
unstable log segment of the Raft log.  It is called by the **leader** when appending
new entries to its own log, and by the **follower** after receiving an AppendEntries
message that has already passed the consistency check (the `maybe_append` gate).

The function is responsible for:
1. Rejecting any batch that would overwrite committed entries (panics on violation).
2. Delegating actual truncation and extension to `unstable.truncate_and_append`.
3. Returning the new `last_index()` so callers can update `nextIndex` or acknowledgement
   metadata.

---

## Structure of the Raft Log

The `RaftLog<T>` combines two log segments:
- **Stable storage** (`store: T`): entries that have been persisted; read-only here.
- **Unstable log** (`unstable: Unstable`): entries not yet written to stable storage;
  can be overwritten by `append`.

The key index variables are:
- `committed`: the highest log index known to be committed (monotone, never decreases).
- `persisted`: the highest index written to stable storage (bookkeeping).
- `unstable.offset`: the first index in the unstable segment.
- `last_index()`: `max` over the unstable and stable segments.

---

## Preconditions

1. **Non-empty batch implies safe start index**:
   If `ents` is non-empty, then `ents[0].index ≥ 1` (log indices are 1-based) and
   `ents[0].index - 1 ≥ committed`.
   
   Equivalently: the batch does not begin before or at the committed boundary.
   The committed prefix of the log is immutable; entries at or before `committed` must
   never be truncated or replaced.  Violation causes a `fatal!` (panic).

2. **Entries form a contiguous sequence** (not enforced by `append` itself, but required
   for a well-formed log): `ents[i].index = ents[0].index + i` for all `i`.

3. **Entry indices are strictly increasing** in the batch.

---

## Postconditions

### P1 — Empty batch is a no-op
If `ents` is empty then the log is unchanged and the return value equals the old
`last_index()`.

### P2 — Return value is `last_index()` after the operation
The function returns the new `last_index()`, which equals
`max(stable.last_index(), unstable.maybe_last_index())` after the call.

### P3 — Return value is the index of the last entry in the batch (if non-empty)
If `ents` is non-empty, the return value equals `ents.last().index`.

This follows because `truncate_and_append` places exactly `ents` starting at
`ents[0].index`, and the unstable segment's new last index is therefore `ents.last().index`.
(When `ents.last().index > old_last_index()`, the unstable segment extends; otherwise,
it is a suffix replacement.)

### P4 — Committed prefix is preserved
Entries at indices `1 .. committed` are unchanged after the call.  The fatal-guard
enforces this: only indices ≥ `ents[0].index = after + 1 > committed` can be affected.

### P5 — Log prefix up to `ents[0].index - 1` is preserved
For every index `k ≤ ents[0].index - 1 = after`, the log term at `k` is unchanged.
This is because `truncate_and_append` only touches entries at index ≥ `ents[0].index`
(it truncates the unstable segment to exactly `after` entries before appending).

### P6 — Log suffix matches the batch exactly
After the call, for every `j ∈ 0 .. ents.len()`, the log entry at index
`ents[0].index + j` equals `ents[j]`.

### P7 — Entries beyond the batch are discarded
Entries at indices `> ents.last().index` that previously resided only in the unstable
segment are discarded.  (Stable storage is never mutated; only the unstable segment is
truncated.)

### P8 — Committed does not decrease
The call never modifies `committed`.

---

## Invariants

### I1 — No-overwrite of committed
`committed ≤ last_index()` before and after every call.  The fatal-guard ensures that
`ents[0].index - 1 ≥ committed`, i.e., the batch starts strictly after the committed
boundary.  Therefore no committed entry is overwritten.

### I2 — Unstable offset remains ≤ `ents[0].index`
After `truncate_and_append`, the unstable offset may decrease (if the new batch starts
before the current offset) or stay the same.  It never exceeds `ents[0].index`.

### I3 — Log term at committed index is preserved
Because the committed prefix is preserved (P4), the term at `committed` in the log is
the same before and after the call.

---

## Edge Cases

### E1 — Empty entry slice
`append(&[])` returns `last_index()` immediately without touching the log.  No-op.

### E2 — Batch that exactly continues the log
If `ents[0].index = last_index() + 1`, the batch appends without conflict.  The
`truncate_and_append` implementation handles this as the "append directly" branch
(the `after` pointer equals `offset + entries.len()`).

### E3 — Batch that conflicts partway through the unstable segment
If `ents[0].index` is strictly between `unstable.offset` and `unstable.offset + entries.len()`,
the unstable entries from `ents[0].index` onward are truncated, then `ents` is appended.
Entries before `ents[0].index` in the unstable segment are preserved.

### E4 — Batch that starts before the unstable offset
If `ents[0].index ≤ unstable.offset`, the entire unstable segment is replaced: the new
offset is set to `ents[0].index` and the full batch replaces the previous entries.

### E5 — Batch that starts at or before committed (fatal)
If `ents[0].index - 1 < committed`, the call panics (`fatal!`).  This is the primary
safety guard.

### E6 — Single-entry batch
Behaves the same as the general case; returns the index of that entry.

---

## Examples

(Based on `test_append` in `src/raft_log.rs`; stable storage initially has entries
`[(index=1, term=1), (index=2, term=2)]`, committed = 0.)

| Input `ents` | Return value | Log after |
|---|---|---|
| `[]` | 2 | `[(1,1),(2,2)]` (unchanged) |
| `[(3,2)]` | 3 | `[(1,1),(2,2),(3,2)]` |
| `[(1,2)]` | 1 | `[(1,2)]` (conflicts from index 1) |
| `[(2,3),(3,3)]` | 3 | `[(1,1),(2,3),(3,3)]` (conflicts from index 2) |

---

## Inferred Intent

`RaftLog::append` is the **leader-side** counterpart to `maybe_append` (the
follower-side entry-acceptance path).  While `maybe_append` checks the consistency of
the incoming `prevLogIndex`/`prevLogTerm` before accepting entries, `append` is called
when the caller already knows the batch is valid and simply wants to write it.

The only correctness guard `append` must maintain is that committed entries are never
overwritten.  All other logic (conflict detection, truncation, extension) is delegated to
`unstable.truncate_and_append` — which is already formally specified in
`FVSquad/LogUnstable.lean`.

This means the formal Lean spec for `raft_log_append` should be relatively thin:
it states the committed-prefix-preservation invariant (P4/P5) and the suffix-exact-match
postcondition (P6), delegating the `truncate_and_append` correctness to the existing
`LogUnstable.lean` lemmas.

---

## Open Questions

1. **Interplay with `persisted`**: After `append`, entries in the unstable segment are
   not yet persisted.  The spec does not say anything about the relationship between the
   new `last_index()` and `persisted`.  Is it always the case that after `append`,
   `persisted < last_index()`?  Only if the batch adds indices beyond what has already
   been written to stable storage.  This is worth clarifying for the Lean model.

2. **Entry payload versus term**: The current `LogUnstable.lean` model abstracts away
   payloads and tracks only terms.  The postcondition P6 says "the log entry equals
   `ents[j]`".  In the Lean model, this reduces to: the log *term* at index
   `ents[0].index + j` equals `ents[j].term`.  Is this sufficient for the safety proof,
   or do we need to track payloads?

3. **Interaction with snapshots**: If the unstable segment contains a pending snapshot,
   `truncate_and_append` replaces it if the new batch starts at or before the snapshot
   index.  The informal spec above does not fully characterise this case.  For the Lean
   spec, we may want to add a precondition that no pending snapshot conflicts with the
   new batch, or handle it as an explicit case.

---

*Informal spec written by Lean Squad (Run 44) as input for Task 3 (Lean 4 formal
specification) of `raft_log_append`.*
