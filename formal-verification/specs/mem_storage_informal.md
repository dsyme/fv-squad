# Informal Specification: `MemStorageCore` Log Operations

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: `src/storage.rs`, `MemStorageCore` struct, lines ~165–370

---

## Purpose

`MemStorageCore` is the in-memory backing store for a Raft log. It maintains:

1. A **snapshot region**: entries up to `snapshot_metadata.index` have been compacted away.
2. An **entries region**: a contiguous slice of `Entry` values at indices `[first_index(), last_index()]`.

The four key operations modelled here are:
- `first_index()` — returns the index of the oldest retained entry
- `last_index()` — returns the index of the newest retained entry
- `compact(compact_index)` — discards entries prior to `compact_index`
- `append(ents)` — truncates-and-extends the log at the first new entry's index
- `term(idx)` — returns the term of the entry at a given log index

---

## Data Model

```
MemStorageCore {
  snapshot_metadata.index : u64   -- last compacted index (0 if no snapshot)
  entries                 : Vec<Entry>  -- contiguous retained entries
}
```

**Contiguity invariant**: `entries[i].index = first_index() + i` for all `0 ≤ i < entries.len()`.
This invariant is maintained by all operations.

**Index arithmetic**:
- `first_index() = entries[0].index` (or `snapshot_metadata.index + 1` when empty)
- `last_index() = entries.last().index` (or `snapshot_metadata.index` when empty)

**Abstract Lean model**:
- `snapshotIndex : Nat` — the last compacted index
- `terms : List Nat` — `terms[i]` is the term of entry at index `snapshotIndex + 1 + i`

The contiguity invariant is baked into the structure by construction.

---

## Preconditions

### `compact(compact_index)`
- `compact_index ≥ 1`
- `compact_index ≤ last_index() + 1` (panics otherwise)
- If `compact_index ≤ first_index()`, this is a no-op (not an error)

### `append(ents)`
- `ents` must be non-empty (early return if empty)
- `ents[0].index ≥ first_index()` (cannot overwrite compacted entries — panics otherwise)
- `ents[0].index ≤ last_index() + 1` (no gap — panics otherwise)

### `term(idx)`
- `idx ≥ snapshot_metadata.index` (the term of the snapshot index is retained)
- `idx ≤ last_index()` (out-of-range returns `Error::Store(StorageError::Unavailable)`)

---

## Postconditions

### `first_index()`
- Always returns `snapshot_metadata.index + 1` when `entries` is empty
- Returns `entries[0].index` when non-empty
- **Invariant**: `first_index() = snapshotIndex + 1` always holds

### `last_index()`
- Returns `snapshot_metadata.index` when `entries` is empty (= `first_index() - 1`)
- Returns `entries.last().index` when non-empty
- **Invariant**: `first_index() ≤ last_index() + 1` always

### `compact(compact_index)` (success path)
- **Effect on `first_index`**: `first_index()' = max(first_index(), compact_index)`
- **Effect on `last_index`**: `last_index()' = last_index()` (unchanged)
- **Effect on entries**: entries at indices `[compact_index, last_index()]` are retained
- **No-op condition**: if `compact_index ≤ first_index()`, nothing changes

### `append(ents)` (success path, non-empty input)
- **Effect on `first_index`**: unchanged (`snapshot_metadata.index` is not modified)
- **Effect on `last_index`**: `last_index()' = ents.last().index`
- **Effect on entries**: entries at indices `[first_index(), ents[0].index)` are retained;
  entries at indices `[ents[0].index, last_index()]` are replaced by `ents`
- **Idempotency**: appending the same entries twice yields the same result as appending once

### `term(idx)` (success path)
- Returns `snapshot_metadata.term` if `idx = snapshot_metadata.index`
- Returns `entries[idx - first_index()].term` if `first_index() ≤ idx ≤ last_index()`

---

## Invariants

1. **Contiguity**: `entries[i].index = first_index() + i` for all `i`
2. **Non-negative range**: `first_index() ≤ last_index() + 1` always
3. **Snapshot boundary**: `snapshot_metadata.index + 1 = first_index()` always
4. **compact monotone**: `compact` never decreases `first_index()`
5. **append preserves firstIndex**: `append` never changes `first_index()`

---

## Edge Cases

- **Empty log**: `entries.is_empty()`, `first_index() = snapshot_metadata.index + 1`,
  `last_index() = snapshot_metadata.index`.  The range `[first_index(), last_index()]` is empty
  (`first_index() > last_index()`).
- **Compact to current firstIndex**: no-op (entries not empty after this).
- **Compact to lastIndex + 1**: log becomes empty (entries all discarded).
- **Append at firstIndex**: replaces the entire log tail.
- **Append at lastIndex + 1**: extends without truncation.
- **term at snapshot boundary**: `term(snapshot_metadata.index)` = `snapshot_metadata.term`.

---

## Examples

Initial state: `snapshotIndex = 3`, `terms = [1, 1, 1]` (entries at indices 4, 5, 6).
- `firstIndex = 4`, `lastIndex = 6`, `entryCount = 3`
- `compact(5)` → `snapshotIndex = 4`, `terms = [1, 1]` → `firstIndex = 5`, `lastIndex = 6`
- `append(startIndex=5, terms=[2])` → `snapshotIndex = 3`, `terms = [1, 2]` → `firstIndex = 4`, `lastIndex = 5`
- `append(startIndex=7, terms=[2])` → `snapshotIndex = 3`, `terms = [1,1,1,2]` → `firstIndex = 4`, `lastIndex = 7`

---

## Open Questions

1. **Snapshot term retention**: `term(snapshot_metadata.index)` returns `snapshot_metadata.term`,
   not an entry term. The Lean model currently ignores terms entirely (they are not modelled
   in the `MemStorageCore` struct). Should the model be extended to track terms?
2. **`apply_snapshot`**: not modelled — it resets both `snapshot_metadata` and clears entries.
   Does any proved property need to account for snapshot application?
3. **Error path semantics**: the Lean model only covers success paths. Should there be separate
   theorems about precondition violation (panic) paths?

---

🔬 *Lean Squad — informal spec written for `dsyme/raft-lean-squad`, Run 125.*
