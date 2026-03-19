# Informal Specification — `Unstable` Log Buffer

> 🔬 *Lean Squad — informal specification extracted from `src/log_unstable.rs`.*

## Purpose

`Unstable` holds the "unstable" portion of the Raft log: entries that have been
received but not yet persisted to stable storage, and/or an incoming snapshot that
has not yet been applied.  It is the in-memory buffer between Raft consensus and the
application's storage layer.

The key design constraint is the **index-offset representation**:
entry `entries[i]` always has Raft log index `offset + i`.  This lets the buffer be
addressed by log index using simple arithmetic.

---

## Representation Fields

| Field        | Type             | Role |
|--------------|------------------|------|
| `offset`     | `u64`            | Raft log index of `entries[0]` |
| `entries`    | `Vec<Entry>`     | Unstable entries not yet persisted |
| `snapshot`   | `Option<Snapshot>` | Incoming snapshot pending application |
| `entries_size` | `usize`        | Approximate byte count (performance field, not verified here) |
| `logger`     | `Logger`         | Side-effect only; omitted from model |

---

## Preconditions (Representation Invariant)

**INV-1 (index coherence)**:
For all `i` in `0..entries.len()`:  `entries[i].index == offset + i`.

**INV-2 (snapshot-offset ordering)**:
If `snapshot = Some(snap)` and `entries` is non-empty, then
`snap.metadata.index < offset`
(the snapshot is older than or equal to the entry immediately before the
first unstable entry; the snapshot cannot overlap the unstable entries).

**INV-3 (offset monotonicity under stable_entries)**:
`offset` only ever increases; once entries are made stable the offset advances
past them and they are cleared from the buffer.

---

## Method Specifications

### `maybe_first_index() → Option<u64>`

**Precondition**: —

**Postcondition**:
- Returns `Some(snap.metadata.index + 1)` if `snapshot = Some(snap)`.
- Returns `None` if `snapshot = None`.

**Rationale**: when a snapshot is pending, the first *new* entry that could follow it
has index `snap.metadata.index + 1`.

---

### `maybe_last_index() → Option<u64>`

**Precondition**: —

**Postcondition**:
- If `entries` is non-empty: returns `Some(offset + entries.len() - 1)`.
- If `entries` is empty and `snapshot = Some(snap)`: returns `Some(snap.metadata.index)`.
- If `entries` is empty and `snapshot = None`: returns `None`.

**Rationale**: the last unstable index is either the last entry's index (by INV-1)
or the snapshot's index if no entries exist.

---

### `maybe_term(idx: u64) → Option<u64>`

**Precondition**: —

**Postcondition**:
- If `idx < offset`:
  - If `snapshot = Some(snap)` and `idx == snap.metadata.index`: returns `Some(snap.metadata.term)`.
  - Otherwise: returns `None`.
- If `idx >= offset`:
  - If `idx > offset + entries.len() - 1` (out of range): returns `None`.
  - Otherwise: returns `Some(entries[idx - offset].term)`.

**Inferred intent**: lookup by Raft log index; returns the term of that entry or None
if the index is outside the known range.

**Open question**: what is the specified behavior when `entries` is empty and `idx ≥ offset`?
Looking at the code: `maybe_last_index()` returns None → `and_then(|last| ...)` returns None. ✓

---

### `stable_entries(index: u64, term: u64)`

**Precondition**:
- `snapshot = None` (the snapshot must already be stable before entries are made stable).
- `entries` is non-empty.
- `entries.last().index == index` and `entries.last().term == term`
  (the caller must confirm the last entry matches).

**Postcondition**:
- `entries` is cleared.
- `entries_size` = 0.
- `offset` = `old_offset + old_entries.len()` (advances past all cleared entries).
- `snapshot` = None (unchanged).

**Invariant maintenance**: INV-1 is trivially satisfied for an empty `entries` list.

---

### `stable_snap(index: u64)`

**Precondition**:
- `snapshot = Some(snap)` with `snap.metadata.index == index`.

**Postcondition**:
- `snapshot = None`.
- `entries` and `offset` are unchanged.

---

### `restore(snap: Snapshot)`

**Precondition**: —

**Postcondition**:
- `entries` is cleared, `entries_size` = 0.
- `offset` = `snap.metadata.index + 1`.
- `snapshot = Some(snap)`.

**Invariant maintenance**: INV-1 satisfied (empty entries); INV-2 satisfied (no entries).

---

### `truncate_and_append(ents: &[Entry])`

**Precondition**:
- `ents` is non-empty.
- `ents` satisfies INV-1: `ents[i].index == ents[0].index + i`.

**Let** `after = ents[0].index`.

**Case A** (`after == offset + entries.len()`):
Entries append directly (no truncation needed).

**Postcondition A**:
- `entries` = `old_entries ++ ents`.
- `offset` unchanged.

**Case B** (`after <= offset`):
The new entries cover or precede the existing unstable window; replace entirely.

**Postcondition B**:
- `entries` = `ents`.
- `offset` = `after`.

**Case C** (`offset < after < offset + entries.len()`):
Truncate the existing entries to keep only indices `[offset, after)`, then append.

**Postcondition C**:
- `entries` = `old_entries[..after - offset] ++ ents`.
- `offset` unchanged.

**Invariant maintenance**: INV-1 is maintained in all three cases because `ents`
is internally coherent and, in Case C, `old_entries[..k]` still satisfies INV-1
(indices `offset..offset+k-1`), and appending `ents` starting at `after = offset + k`
preserves the invariant for the combined list.

---

### `slice(lo: u64, hi: u64) → &[Entry]`

**Precondition**:
- `lo ≤ hi`.
- `offset ≤ lo` and `hi ≤ offset + entries.len()`.

**Postcondition**:
- Returns `entries[lo - offset .. hi - offset]`.
- Each returned entry at position `k` has index `lo + k` (follows from INV-1).

---

## Edge Cases

| Condition | Behaviour |
|-----------|-----------|
| `maybe_first_index` with no snapshot | Returns `None` |
| `maybe_last_index` with no snapshot and no entries | Returns `None` |
| `maybe_term` with index below snapshot range | Returns `None` |
| `truncate_and_append` with `after == offset + entries.len()` | Pure append |
| `truncate_and_append` with `after < offset` | Full replacement |
| `stable_entries` called with empty entries | Fatal panic (precondition violation) |
| `stable_snap` called with no snapshot | Fatal panic (precondition violation) |

---

## Examples (from tests)

```
entries = [(5,1)], offset = 5, snapshot = Some((4,1))
  maybe_first_index() = Some(5)  (snap.index + 1 = 4 + 1)
  maybe_last_index()  = Some(5)  (offset + len - 1 = 5 + 1 - 1)
  maybe_term(5)       = Some(1)  (entries[5-5].term = entries[0].term)
  maybe_term(4)       = Some(1)  (snap.index == 4)

truncate_and_append on entries=[(5,1),(6,1),(7,1)], offset=5 with ents=[(6,2)]:
  after = 6; 5 < 6 < 5+3; truncate to entries[..1] = [(5,1)]; append [(6,2)]
  result: entries = [(5,1),(6,2)], offset = 5

restore(snap=(6,2)):
  entries = [], offset = 7, snapshot = Some((6,2))
```

---

## Open Questions

1. **`entries_size` overflow**: the Rust code uses `usize` subtraction in `truncate_and_append`
   which could panic if `entries_size` underflows.  Is this considered a bug or intentional?

2. **`stable_entries` precondition**: the code panics if entries is empty or if the last
   entry does not match.  Are these considered API misuse (caller responsibility) or
   should the function return an error?

3. **Joint use of snapshot + entries**: the code does not seem to validate that
   `snap.metadata.index + 1 == offset` when entries are present.  Is `snap.metadata.index < offset`
   sufficient, or should equality be required?

---

## Inferred Intent

The `Unstable` buffer acts as a FIFO queue of log entries indexed by Raft log index.
It supports:
1. **Query**: what is the last known index? what is the term at a given index?
2. **Append/truncate**: add new entries, potentially overwriting a suffix.
3. **Commit**: advance the stable offset when entries are persisted.
4. **Snapshot**: replace the buffer with a snapshot when a peer sends one.

The central invariant (INV-1) ensures that the Vec index and Raft log index always
agree, making O(1) lookup possible without scanning.
