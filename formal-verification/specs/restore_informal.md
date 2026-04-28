# Informal Specification: `RaftLog::restore`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Purpose

`RaftLog::restore` applies an incoming snapshot to the Raft log. This is used when a
follower is far behind and the leader sends a snapshot instead of individual log entries.
The function resets the log state so that the snapshot's index becomes the new baseline.

## Source

- **File**: `src/raft_log.rs`, line ~696
- **Signature**: `pub fn restore(&mut self, snapshot: Snapshot)`
- **Related**: `Unstable::restore` in `src/log_unstable.rs`

## Preconditions

1. `snapshot.get_metadata().index >= self.committed` — the snapshot must not regress below
   the current commit point. The Rust code asserts this.

## Postconditions

1. **Committed advances**: `self.committed == snapshot.get_metadata().index` after the call.
2. **Persisted is bounded**: `self.persisted <= self.committed`. Specifically:
   - If `persisted > committed` (old committed) before the call, persisted is reset to the
     old committed value, then committed is advanced.
   - Result: `persisted <= committed` (new committed).
3. **Unstable state reset**: `self.unstable.restore(snapshot)` is called, which:
   - Clears all unstable entries
   - Sets `offset = snapshot_index + 1`
   - Stores the snapshot

## Invariants Maintained

1. `applied <= persisted <= committed` — the core Raft log ordering invariant.
   (Note: `applied` is not modified by `restore`, so `applied <= persisted` must hold
   from the precondition.)
2. `committed <= last_index` — committed never exceeds the log length. After restore,
   `last_index` is at least `snapshot_index` (from unstable offset).

## Edge Cases

1. **Snapshot index == committed**: no-op for committed, persisted may still be clamped.
2. **Persisted > committed (old)**: persisted is reset to old committed before committed advances.
3. **Persisted <= committed (old)**: persisted is not modified (it's already bounded).

## Examples

| Before (committed, persisted) | Snapshot index | After (committed, persisted) |
|-------------------------------|----------------|------------------------------|
| (5, 3) | 10 | (10, 3) |
| (5, 7) | 10 | (10, 5) |
| (5, 5) | 5  | (5, 5) |
| (5, 5) | 10 | (10, 5) |

## Open Questions

1. The assertion `index >= self.committed` means the function panics on stale snapshots.
   Should a non-panicking model return `Option` instead?
2. The interaction between `persisted` clamping and the `max_apply_unpersisted_log_limit`
   is subtle — the comment in the source code explains the reasoning.

## Inferred Intent

The function ensures the log can be fast-forwarded to a snapshot state without violating
the `persisted <= committed` invariant, even if some entries had been persisted beyond the
old commit point. The persisted-clamping logic prevents a situation where `persisted` points
to entries that no longer exist after the snapshot restore.
