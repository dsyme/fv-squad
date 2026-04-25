# Informal Specification: `has_next_entries_since` / `applied_index_upper_bound`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Target

- **File**: `src/raft_log.rs`
- **Functions**: `RaftLog::has_next_entries_since`, `RaftLog::has_next_entries`,
  `RaftLog::applied_index_upper_bound`
- **Run**: 111 (Lean Squad)

---

## Purpose

`applied_index_upper_bound` computes the highest log index that *may* be applied at any
given moment.  Normally this equals `committed`, but when the configuration option
`max_apply_unpersisted_log_limit > 0` is set, entries may be applied *before* they are
fully persisted — up to `persisted + max_apply_unpersisted_log_limit` at most.

`has_next_entries_since(since_idx)` answers whether there are any committed (or
"apply-ready") log entries that have not yet been applied since `since_idx`.

`has_next_entries` is a convenience wrapper that calls `has_next_entries_since(self.applied)`.

---

## Preconditions

For `applied_index_upper_bound`:
- `committed`, `persisted`, and `max_apply_unpersisted_log_limit` are non-negative integers.
- No additional preconditions — the function is total.

For `has_next_entries_since(since_idx)`:
- `first_index` ≤ `last_index + 1` (the log may be empty).
- `since_idx` can be any value; if it is greater than the upper bound, the function returns `false`.

---

## Postconditions

### `applied_index_upper_bound`

Returns:
```
min(committed, persisted + max_apply_unpersisted_log_limit)
```

Key properties:
1. **Bounded above by `committed`**: the returned value never exceeds `committed`.
2. **Bounded above by `persisted + limit`**: the returned value never exceeds
   `persisted + max_apply_unpersisted_log_limit`.
3. **Equals `committed` when limit is large**: if `persisted + limit ≥ committed`,
   the result is exactly `committed`.
4. **Equals `persisted + limit` when tightly constrained**: if `persisted + limit < committed`,
   the result is `persisted + limit`.
5. **Monotone in `committed`**: increasing `committed` never decreases the result.
6. **Monotone in `persisted`**: increasing `persisted` never decreases the result.
7. **Monotone in `limit`**: increasing `max_apply_unpersisted_log_limit` never decreases
   the result.

### `has_next_entries_since(since_idx)`

Let:
- `offset = max(since_idx + 1, first_index)`
- `high = applied_index_upper_bound(committed, persisted, limit)`

Returns `true` iff `high + 1 > offset`, i.e. `high ≥ offset`, i.e. there is at least one
index in `[offset, high]`.

Key properties:
1. **Returns `false` when `since_idx ≥ high`**: if `since_idx` is at or beyond the
   apply-ready upper bound, there are no new entries to apply.
2. **Returns `false` when `committed = 0` and `first_index > 0`**: empty committed range.
3. **Anti-monotone in `since_idx`**: if the function returns `true` for `since_idx = k`,
   it also returns `true` for all `j ≤ k`.
4. **Monotone in `committed`**: increasing `committed` can only turn `false` to `true`.
5. **Monotone in `persisted`**: increasing `persisted` can only turn `false` to `true`.
6. **Consistent with `next_entries`**: `has_next_entries_since` is `true` iff
   `next_entries_since` would return `Some`.

### `has_next_entries`

`has_next_entries()` is identical to `has_next_entries_since(self.applied)`.

---

## Invariants

- `applied ≤ applied_index_upper_bound`: the applied pointer never exceeds the upper bound
  (otherwise entries would have been applied past the allowed limit).
- When `max_apply_unpersisted_log_limit = 0`, `applied_index_upper_bound = min(committed, persisted)`.
  In this "safe sync" mode, entries are never applied before persistence.

---

## Edge Cases

1. **Empty log** (`committed = 0`, `first_index = 1`): `high = 0`, `offset ≥ 1`, so
   `has_next_entries_since` returns `false`.
2. **`since_idx + 1` overflows**: in the Rust code `since_idx` is a `u64`; we model all
   indices as `Nat` so overflow does not apply.
3. **`persisted + limit` overflows**: similarly, modelled with `Nat` arithmetic.
4. **`since_idx = 0`**: `offset = max(1, first_index) = first_index` (since first_index ≥ 1).
5. **Large `since_idx` (well past committed)**: `has_next_entries_since` returns `false`.

---

## Examples

| `committed` | `persisted` | `limit` | `upper_bound` |
|-------------|-------------|---------|---------------|
| 10          | 8           | 0       | 8             |
| 10          | 8           | 5       | 10            |
| 10          | 8           | 2       | 10            |
| 10          | 5           | 2       | 7             |
| 0           | 5           | 2       | 0             |

| `first_index` | `committed` | `persisted` | `limit` | `since_idx` | Result |
|---------------|-------------|-------------|---------|-------------|--------|
| 1             | 5           | 5           | 0       | 2           | true   |
| 1             | 5           | 5           | 0       | 5           | false  |
| 1             | 5           | 3           | 0       | 2           | true   |
| 1             | 5           | 3           | 0       | 3           | false  |
| 1             | 5           | 3           | 3       | 4           | true   |
| 1             | 0           | 0           | 0       | 0           | false  |

---

## Open Questions

1. **What guarantees that `applied ≤ applied_index_upper_bound` is maintained?**
   The Raft implementation tracks this invariant informally; a future formal invariant
   could prove it inductively over the state machine.

2. **When can `persisted + limit < committed`?**
   This happens during rapid leader activity where entries are committed faster than they
   can be written to stable storage — the limit allows the application layer to process
   entries ahead of persistence for throughput.

---

## Inferred Intent

The `applied_index_upper_bound` function bridges committed-log entries and the persistence
layer.  By computing `min(committed, persisted + limit)`, it allows a configurable degree of
optimistic application while keeping safety (never applying uncommitted entries) and
optionally providing a hard bound on how far ahead of persistence we can apply.

`has_next_entries_since` is intended as an *efficient check* before calling the more
expensive `next_entries_since` — callers should invoke `next_entries_since` only when
`has_next_entries_since` returns `true`.
