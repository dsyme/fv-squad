# Informal Specification: `RaftLog::maybe_persist`

> 🔬 *Lean Squad — auto-generated informal specification.*

**Source**: `src/raft_log.rs`, `pub fn maybe_persist(&mut self, index: u64, term: u64) -> bool`

---

## Purpose

`maybe_persist` is called by a Raft node when it has durably written log entries to
stable storage (via an asynchronous I/O path).  It attempts to advance the `persisted`
index — the highest log position confirmed written to stable storage on this node.

The function must be conservative: it must **not** advance `persisted` past
`first_update_index`, which is the lower bound of entries that may still be in-flight
(not yet durably stored).  Advancing past this boundary could cause the node to claim a
log position is persisted when it has not actually been flushed.

---

## State involved

| Field | Type | Meaning |
|-------|------|---------|
| `self.persisted` | `u64` | Highest durably persisted log index on this node |
| `self.unstable.offset` | `u64` | First log index in the unstable buffer |
| `self.unstable.snapshot` | `Option<Snapshot>` | A pending snapshot (not yet applied) |
| `self.store.term(idx)` | `Result<u64>` | Term of the log entry at index `idx` in stable storage |

---

## Preconditions

1. `self.persisted < self.unstable.offset` — maintained as a class invariant.
2. If a pending snapshot exists, its metadata index satisfies
   `snap.metadata.index ≤ self.unstable.offset` — another class invariant.
3. The caller has already durably written the entry at `(index, term)` to stable storage,
   so `self.store.term(index)` is expected to return `Ok(term)`.

---

## `first_update_index`

```
first_update_index =
    if unstable.snapshot is Some(s) then s.metadata.index
    else unstable.offset
```

This is the lowest index at which the unstable buffer or a pending snapshot could
overwrite entries — an upper exclusive bound for safely advancing `persisted`.

---

## Postconditions

**Returns `true` (persisted advanced) iff all of the following hold:**

1. `index > self.persisted`                  — the proposed index is strictly newer
2. `index < first_update_index`              — the proposed index is safely below any in-flight updates
3. `self.store.term(index) == Ok(term)`      — the stored term matches (guards against stale or wrong-term entries)

**When returns `true`**: `self.persisted` is updated to `index`.

**When returns `false`**: the state is **unchanged** (`self.persisted` is not updated).

---

## Invariants maintained

- **`persisted < unstable.offset`** is preserved:
  - On success: `index < first_update_index ≤ unstable.offset`, so new persisted < offset.
  - On failure: state unchanged.

---

## Edge cases

| Scenario | Expected behaviour |
|----------|--------------------|
| `index == self.persisted` | Returns `false` (condition `index > persisted` fails) |
| `index < self.persisted` | Returns `false` (same condition) |
| `index == first_update_index` | Returns `false` (`index < first_update_index` fails — `<` is strict) |
| `index > first_update_index` | Returns `false` |
| `store.term(index) ≠ term` | Returns `false` |
| `store.term(index)` returns `Err` | Returns `false` (`is_ok_and` is false for errors) |
| Snapshot pending (offset < snap.index) | `first_update_index = snap.index`, limits advance further |
| No snapshot, `index = offset - 1` | Returns `true` if term matches and `index > persisted` |

---

## Examples (from `test_maybe_persist_with_snap`)

Setup: `snap_index = 5, snap_term = 2`.  After restoring snapshot, `persisted = 5`.

| `(stablei, stablet, new_entries)` | `wpersisted` | Why |
|-----------------------------------|-------------|-----|
| `(6, 2, [])` | 5 | No new entries → store doesn't have term 6 |
| `(6, 2, [entry(6,2)])` | 6 | After stable_entries; `6 < snap.index=5`? No — with snap present and snap.index=5, first_update_index=5, so 6 < 5 fails → still 5. Wait: persisted 5, index 6, first_update_index = snap.index = 5 → `6 < 5` fails. |

A further test: after `restore(snap=100, term=1)`, `unstable.offset = 101`, no pending snapshot:
- `maybe_persist(101, 1)` → `false` (because `101 < offset(101)` fails — `<` is strict)
- `maybe_persist(102, 1)` after appending entry 102 → `false` (`102 ≥ offset=101`)

---

## Inferred Intent

The strict `<` on `first_update_index` is deliberate: it prevents a race where an entry
at `offset` is simultaneously being written to storage and claimed as persisted.  The
comment in the source explains an observed corner case in a 5-node cluster where this
protection is essential.

---

## Open Questions

1. Can `first_update_index` ever be 0?  (If so, no index can pass the condition.)
2. Is `store.term(index)` always consistent with entries that were written via
   `stable_entries`?  The spec assumes yes, but failure paths are not modelled.
3. Under what invariants does `snap.metadata.index ≤ unstable.offset` hold?
   This is assumed as a WF precondition in the Lean model.
