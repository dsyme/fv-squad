# Informal Specification: `RaftLog::restore`

**Target**: `src/raft_log.rs` — `RaftLog::restore(snapshot: Snapshot)`
(also delegates to `log_unstable.rs` — `Unstable::restore(snap: Snapshot)`)

---

## Purpose

`RaftLog::restore` installs a Raft snapshot as the new authoritative state of the log.
When a follower is severely lagging behind, the leader sends it a complete snapshot
instead of individual log entries.  This function transitions the log to be rooted at
the snapshot's commit point:

1. It verifies the snapshot is not older than the current committed index.
2. It resets `committed` to the snapshot's index (the snapshot represents a fully
   committed state up to that index).
3. It resets `persisted` to respect the new committed value (details below).
4. It delegates to `Unstable::restore`, which clears all in-memory unstable entries and
   installs the snapshot as the new pending unstable snapshot with offset set to
   `snapshot.index + 1`.

---

## Preconditions

- **`snapshot.index >= committed`**: The snapshot must be at least as recent as the
  last committed index.  Violation triggers an assertion panic.
  (Equivalently: snapshots may not roll back committed state.)

---

## Postconditions

Let `snap_idx = snapshot.get_metadata().index`.

### Fields changed

| Field | Before | After | Comment |
|-------|--------|-------|---------|
| `committed` | `c` | `snap_idx` | Advanced to snapshot index |
| `persisted` | `p` | `min(c, p)` = `if p > c then c else p` | Clamped to old committed |
| `unstable.entries` | any | `[]` | All in-memory entries discarded |
| `unstable.entries_size` | any | `0` | Cleared |
| `unstable.offset` | `o` | `snap_idx + 1` | Reset to entry after snapshot |
| `unstable.snapshot` | any | `Some(snapshot)` | New pending snapshot |

### Fields unchanged

| Field | Comment |
|-------|---------|
| `applied` | Not modified by `restore` |
| `store` | Storage backend not touched |
| `max_apply_unpersisted_log_limit` | Unchanged |

---

## Invariants Maintained

The following `RaftLog` invariants hold after `restore`:

1. **Committed monotonicity**: `committed' >= committed` (since `snap_idx >= c` by precondition).
2. **persisted ≤ committed**: `persisted' <= committed'`.
   - Case `p > c`: `persisted' = c <= snap_idx = committed'`. ✓
   - Case `p <= c`: `persisted' = p <= c <= snap_idx = committed'`. ✓
3. **persisted < unstable.offset**: `persisted' <= committed' = snap_idx < snap_idx + 1 = unstable.offset'`. ✓
4. **unstable.offset = committed + 1**: After restore, `unstable.offset' = snap_idx + 1 = committed' + 1`. ✓

---

## The `persisted` Reset Rationale

The `persisted > committed` reset is subtle.  Before the snapshot:
- Entries in range `(committed, persisted]` were durably written to storage but not
  yet committed (they could still be overwritten by a leader's conflicting entries).
- After the snapshot, entries in that range are replaced by the snapshot.  However,
  the invariant `applied <= min(persisted, committed)` must be preserved.
- Resetting `persisted` to `committed_old` (= min(p, c)) is safe: it doesn't claim
  entries beyond the snapshot's commit point as "persisted," avoiding inconsistency
  with entries that the snapshot supersedes.

---

## Edge Cases

- **`snapshot.index == committed`**: Snapshot exactly at current commit; committed
  doesn't advance.  This is permitted and should be a no-op for `committed`.
- **`snapshot.index > committed` by a large margin**: Normal case for a significantly
  lagging follower.
- **`persisted == committed`**: No clamping needed; `persisted` stays the same; only
  `committed` advances and `unstable` is reset.
- **`persisted < committed`**: Unusual but valid (only during specific recovery paths).
  `persisted` is unchanged; only `committed` and `unstable` are updated.

---

## Examples

### Example 1: Normal restore (persisted ≤ committed)

```
Before: committed=100, persisted=100, unstable.offset=101
restore(snap(index=200, term=3))
After:  committed=200, persisted=100, unstable.offset=201
```

(Verified by `test_restore_snap` in `src/raft_log.rs` lines 1868–1876.)

### Example 2: Restore with persisted > committed

```
Before: committed=200, persisted=209, unstable.offset=210
restore(snap(index=205, term=1))
After:  committed=205, persisted=200, unstable.offset=206
```

(Verified by `test_restore_snap` lines 1893–1896, comment: "persisted should reset to previous commit index(200)".)

### Example 3: Panic case

```
Before: committed=205, persisted=200
restore(snap(index=204, term=1))  -- panics: 204 < 205
```

---

## Open Questions

1. **Applied not modified**: Is it always the case that `applied <= committed` remains
   satisfied after restore, given that `applied` is not reset?  The code comment at
   line 43–46 suggests this invariant may be temporarily violated with
   `max_apply_unpersisted_log_limit > 0`, but not in the standard case.
2. **Snapshot idempotence**: What happens if `restore` is called twice with the same
   snapshot? The assert `snap_idx >= committed` would require `snap_idx >= snap_idx`,
   which is satisfied — so it appears idempotent.

---

🔬 *Lean Squad — automated informal specification extraction (Task 2).*
