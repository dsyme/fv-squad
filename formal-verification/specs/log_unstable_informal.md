# Informal Specification: `Unstable` log segment

**Source**: `src/log_unstable.rs`
**FV Target**: `log_unstable`
**Phase**: 2 (Informal Spec)

---

## Purpose

`Unstable` holds Raft log entries and/or a snapshot that have been received from the
leader but have **not yet been persisted** to stable storage. It tracks a contiguous
"window" of the log.

Entries are stored as a flat `Vec<Entry>`. Entry at position `i` in the vector has log
index `offset + i`. The `offset` field records where the window begins in the global log.
Optionally, a `snapshot` may be pending; its index is always strictly less than `offset`.

---

## Structure

```
snapshot (optional)  |  entries[0..len]
                     ^
                   offset
```

- `offset`: the log index of `entries[0]`. Always `> snapshot.index` when both exist.
- `entries`: terms of pending (unstabilised) log entries.
- `snapshot`: a pending snapshot (index, term), or none.
- `entries_size`: byte count of entries (derived, omitted from the Lean model).

---

## Key Invariant

**Offset correctness**: `entries[i]` has log index `offset + i` for all valid `i`.

**Snapshot ordering**: if `snapshot = Some(sidx, _)` and `entries` is non-empty, then
`sidx < offset` (snapshot predates the first entry).

---

## Preconditions (assumed, not re-checked)

- **`stable_entries(index, term)`**: `entries` is non-empty; the last entry has the given
  index and term. The snapshot is None (must be stabilised first).
- **`stable_snap(index)`**: `snapshot = Some(index, _)`.
- **`truncate_and_append(ents)`**: `ents` is non-empty.
- **`slice(lo, hi)`**: `offset ≤ lo ≤ hi ≤ offset + entries.length`.

---

## Function Specifications

### `maybe_first_index() → Option<u64>`

**Postcondition**: returns `Some(snapshot.index + 1)` iff a snapshot is pending, else None.

### `maybe_last_index() → Option<u64>`

**Postcondition**:
- If `entries` non-empty: returns `Some(offset + entries.len() - 1)`.
- Else if snapshot present: returns `Some(snapshot.index)`.
- Else: returns `None`.

### `maybe_term(idx) → Option<u64>`

**Postcondition**:
- If `idx < offset`:
  - If snapshot present and `idx = snapshot.index`: returns `Some(snapshot.term)`.
  - Else: returns `None`.
- If `offset ≤ idx < offset + entries.len()`: returns `Some(entries[idx - offset].term)`.
- If `idx ≥ offset + entries.len()`: returns `None`.

### `stable_entries(index, term)` (happy path)

**Precondition**: entries non-empty; `entries.last().index = index`, `entries.last().term = term`.
**Postcondition**: `offset' = offset + entries.len()`, `entries' = []`, snapshot unchanged.
**Effect**: advances the "start of unstable window" past all entries.

### `stable_snap(index)` (happy path)

**Precondition**: `snapshot = Some(index, _)`.
**Postcondition**: `snapshot' = None`; entries and offset unchanged.

### `restore(snap)`

**Postcondition**: `offset' = snap.index + 1`, `entries' = []`, `snapshot' = Some(snap)`.
**Effect**: completely replaces unstable state with the new snapshot.

### `truncate_and_append(ents)` (3 cases)

Let `after = ents[0].index`.

**Case 1** (`after = offset + entries.len()`): Append directly.
- `entries' = entries ++ ents_terms`

**Case 2** (`after ≤ offset`): Replace entirely (entries predate current window).
- `offset' = after`, `entries' = ents_terms`

**Case 3** (`offset < after < offset + entries.len()`): Truncate then append.
- `entries' = entries[0..after-offset] ++ ents_terms`

In all cases: `offset` unchanged (except case 2), `snapshot` unchanged.

### `slice(lo, hi)`

**Precondition**: `offset ≤ lo ≤ hi ≤ offset + entries.len()`.
**Postcondition**: returns terms of entries with log indices in `[lo, hi)`.
**Length**: `hi - lo`.

---

## Edge Cases

- Empty entries + no snapshot: `maybe_last_index` and `maybe_first_index` return None.
- `stable_entries` on single entry: offset advances by 1, entries cleared.
- `truncate_and_append` case 2 with `after = offset`: replaces entries (common during leader change).
- `restore` always sets entries to empty (snapshot supersedes any pending entries).

---

## Examples

```
u = { offset: 5, entries: [t1, t2, t3], snapshot: None }
  maybe_last_index(u) = Some(7)   -- 5 + 3 - 1
  maybe_term(u, 5) = Some(t1)     -- entries[0]
  maybe_term(u, 6) = Some(t2)     -- entries[1]
  maybe_term(u, 8) = None         -- out of range

truncate_and_append(u, [t4,t5], after=8):  -- case 1 (8 = 5+3)
  entries' = [t1,t2,t3,t4,t5]

truncate_and_append(u, [t4,t5], after=3):  -- case 2 (3 ≤ 5)
  offset'=3, entries'=[t4,t5]

truncate_and_append(u, [t4,t5], after=6):  -- case 3 (5 < 6 < 8)
  entries' = [t1,t4,t5]   -- take(1) ++ [t4,t5]
```

---

## Inferred Intent

The unstable log implements a "write-ahead" buffer. Entries arrive from the leader,
accumulate here, get written to stable storage, then `stable_entries` advances the
window. A snapshot completely resets the buffer. The offset + list representation
is an efficient append-mostly structure with O(1) last-index lookup.

---

## Open Questions

1. **Snapshot ordering after `truncate_and_append` case 2**: if `after ≤ offset` and
   a snapshot is pending, the new offset (`after`) may equal or be less than the snapshot
   index. Is the caller responsible for ensuring the snapshot is cleared before calling
   `truncate_and_append` in case 2? (The Rust code for `stable_entries` asserts `snapshot.is_none()`
   but `truncate_and_append` does not.)

2. **Thread safety**: `Unstable` is used with `&mut self` — it is not shared. No concurrent
   access is assumed in this model.

---

🔬 *Generated by Lean Squad automated formal verification.*
