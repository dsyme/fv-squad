# Informal Specification: `next_entries_since` / `next_entries`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: `src/raft_log.rs`, lines ~447–492

---

## Purpose

`next_entries_since(since_idx, max_size)` returns the batch of log entries that are
ready for application (committed and within the persistence limit) but have not yet
been applied since `since_idx`. It is the primary mechanism by which the Raft state
machine delivers entries to the application layer.

`next_entries(max_size)` is the specialisation where `since_idx = self.applied`.

---

## Implementations

```rust
pub fn next_entries_since(&self, since_idx: u64, max_size: Option<u64>) -> Option<Vec<Entry>> {
    let offset = cmp::max(since_idx + 1, self.first_index());
    let high = self.applied_index_upper_bound() + 1;
    if high > offset {
        match self.slice(offset, high, max_size, GetEntriesContext(...)) {
            Ok(vec) => return Some(vec),
            Err(e) => fatal!(self.unstable.logger, "{}", e),
        }
    }
    None
}

pub fn next_entries(&self, max_size: Option<u64>) -> Option<Vec<Entry>> {
    self.next_entries_since(self.applied, max_size)
}
```

---

## Preconditions

- `since_idx` can be any `u64`; it is the index of the last applied entry (inclusive).
- `max_size` bounds the total byte size of returned entries (a hint, not a hard truncation in the index model).
- `self.first_index()` ≥ 1 always (after snapshot installation or initial state).
- `self.committed ≤ self.last_index()` — only committed entries may be returned.
- `self.persisted + self.max_apply_unpersisted_log_limit ≥ 0` (always true for `u64`).

---

## Postconditions

**Return value**:
- Returns `None` if there are no apply-ready entries beyond `since_idx`.
- Returns `Some(entries)` where `entries` is the non-empty slice
  `log[offset .. upper_bound]` (1-indexed, both ends inclusive), where:
  - `offset = max(since_idx + 1, first_index())`
  - `upper_bound = applied_index_upper_bound()` = `min(committed, persisted + limit)`

**Connection to `has_next_entries_since`**:
- `next_entries_since(since_idx, _) = Some(...)` ↔ `has_next_entries_since(since_idx) = true`
  (i.e., `high > offset`).
- `next_entries_since(since_idx, _) = None` ↔ `has_next_entries_since(since_idx) = false`.

**Monotonicity**:
- If `since_idx ≤ since_idx'`, the returned slice starting at `since_idx` is a prefix
  of (or equal to) the returned slice starting at `since_idx'` — or more precisely,
  `since_idx` can only yield more entries (a superset with a lower start offset).
- If `committed` increases, more entries may become available (monotone in `committed`).
- If `persisted` increases, more entries may become available when `limit > 0`.

**Slice semantics**:
- All entries in the returned slice are at contiguous indices `[offset, upper_bound]`.
- Entry at position `i` in the returned slice has log index `offset + i` (0-based).
- The first returned entry's index equals `offset = max(since_idx + 1, first_index())`.
- The last returned entry's index equals `upper_bound`.

**`max_size` truncation** (ignored in the abstract model):
- When `max_size = None`, the full slice is returned.
- When `max_size = Some(n)`, the slice is truncated so total byte size ≤ `n`.
  The abstract Lean model ignores truncation and always returns the full slice.

---

## Invariants

- The returned entries are a **contiguous sub-sequence** of the committed log segment.
- The returned entries never include index 0 (`first_index() ≥ 1`).
- The returned entries never include entries beyond `upper_bound` (commit/persistence limit).
- All returned entries were previously appended by AppendEntries and acknowledged.

---

## Edge Cases

| Scenario | Expected result |
|----------|----------------|
| `since_idx ≥ upper_bound` | `None` (no apply-ready entries) |
| `since_idx + 1 < first_index()` | Offset clipped to `first_index()` (snapshot gap) |
| `upper_bound = 0` | `None` (nothing committed) |
| `committed = 0` | `None` |
| `persisted + limit < committed` | Only up to `persisted + limit` returned |
| `max_size = None` | Full slice returned |
| `since_idx = applied` | `next_entries` specialisation |

---

## Examples

Using `first_index = 1`, `committed = 5`, `persisted = 5`, `limit = 0`:
- `next_entries_since(3) = Some(entries[4..5])` — indices 4, 5
- `next_entries_since(5) = None` — since_idx ≥ upper_bound
- `next_entries_since(0) = Some(entries[1..5])` — full window

Using `first_index = 1`, `committed = 10`, `persisted = 7`, `limit = 0`:
- `upper_bound = min(10, 7) = 7`
- `next_entries_since(4) = Some(entries[5..7])` — indices 5, 6, 7

---

## Inferred Intent

The function is designed to be called by the Raft client's `Ready` polling loop:
`applied` advances after the application processes each batch. `next_entries()`
naturally delivers the next batch, and `next_entries_since()` allows the caller
to re-request entries from a prior application point if needed.

The `first_index()` clip handles the case where a snapshot was installed at an
index beyond `since_idx` — entries before `first_index()` are no longer available
in the log and must have been captured in the snapshot.

---

## Open Questions

1. **Truncation semantics**: If `max_size` truncates the slice, does the caller
   need to track the exact last-applied index (not just `since_idx`)?  The current
   implementation returns entries in one batch; partial application would require
   the caller to advance `applied` by the actual number of entries consumed.

2. **Empty-log snapshot case**: if `first_index() > committed + 1`, no entries
   are available but the log is not empty either — it just has a gap. Is this
   a valid state? The code does not panic here; it returns `None`.

3. **Re-delivery**: Can `next_entries_since` be called with the same `since_idx`
   multiple times? Yes — the function is pure (read-only) and returns the same
   result each time for fixed state.

---

## Connection to HasNextEntries (HNE1–HNE14)

The boolean companion `has_next_entries_since` is fully formalised in
`FVSquad/HasNextEntries.lean` (HNE1–HNE14, Run 111).  The informal spec above
is the entry-returning counterpart: `next_entries_since` returns a `Some` precisely
when `has_next_entries_since = true`.

The key properties to formalise in Lean:
- **NE1**: `next_entries_since = None` ↔ `has_next_entries_since = false`
- **NE2**: If `Some(es)` returned, `es.len = upper_bound - offset + 1`
- **NE3**: If `Some(es)` returned, `es[i].index = offset + i`
- **NE4**: Anti-monotone in `since_idx`
- **NE5**: Monotone in `committed`
- **NE6**: Monotone in `persisted`
- **NE7**: `next_entries = next_entries_since(applied)`

🔬 *Written by Lean Squad automated formal verification (Run 112).*
