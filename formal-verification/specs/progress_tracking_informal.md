# Informal Specification: `Progress` Tracking Operations

**Source**: `src/tracker/progress.rs` — `Progress::maybe_update`, `update_committed`, `maybe_decr_to`

## Purpose

`Progress` is the leader's per-follower view of replication state in Raft.
Three key mutation methods control how indices advance or retreat:

| Method | Purpose |
|--------|---------|
| `maybe_update(n)` | Advance `matched` (and `next_idx`) when a newer ACK arrives |
| `update_committed(ci)` | Monotonically advance the follower's known `committed_index` |
| `maybe_decr_to(rejected, match_hint, rs)` | Retreat `next_idx` in response to a log-reject message |

Together they implement Raft's replication flow-control: the leader optimistically
probes and replicates, reacting to follower ACKs (maybe_update) and NACKs (maybe_decr_to),
while separately tracking how much of the committed prefix each follower knows about.

---

## `Progress` Fields (relevant subset)

| Field | Type | Meaning |
|-------|------|---------|
| `matched` | `u64` | Highest log index known to be replicated to this follower |
| `next_idx` | `u64` | Next log index to send to this follower |
| `state` | `ProgressState` | `Probe`, `Replicate`, or `Snapshot` |
| `paused` | `bool` | Whether replication is temporarily paused (Probe only) |
| `pending_request_snapshot` | `u64` | Pending snapshot request index (0 = none = `INVALID_INDEX`) |
| `committed_index` | `u64` | Highest committed index this follower has acknowledged |

**Invariant (WF)**: `next_idx ≥ matched + 1` — the next index to send is always strictly
beyond the highest confirmed match.

---

## `maybe_update(n: u64) → bool`

### Purpose
Called when the leader receives an acknowledgement that the follower has replicated
entries up through index `n`. Advances `matched` and ensures `next_idx` stays ahead.

### Preconditions
- `n` is a valid log index (> 0 in practice, but 0 is handled gracefully)
- The WF invariant holds: `next_idx ≥ matched + 1`

### Postconditions
- **Returns `true`** iff `n > matched` (i.e., a genuine advance occurred)
- **Returns `false`** iff `n ≤ matched` (stale or duplicate ACK)
- `matched' = max(matched, n)` — matched never decreases
- `next_idx' = max(next_idx, n + 1)` — next_idx never decreases
- If returns `true`: `paused` is cleared to `false` (resume after probe)
- All other fields (`state`, `committed_index`, `pending_request_snapshot`) unchanged
- WF invariant preserved: `next_idx' ≥ matched' + 1`

### Edge Cases
- `n = 0`: returns `false` (matched is always ≥ 0, so 0 ≤ matched); no change
- `n = matched`: returns `false` (duplicate ACK); next_idx may still advance if n+1 > next_idx
  (though this is unusual in practice)
- `n > matched`: normal case; matched advances, paused is cleared

### Inferred Intent
The dual update of `matched` and `next_idx` (both to at least `n+1`) ensures that even
if a stale ACK arrives for an already-matched index, the next_idx is at least consistent.
The `paused` clear on genuine update is essential: a Probe progress that was paused
(waiting for ACK) is now free to send again.

---

## `update_committed(committed_index: u64)`

### Purpose
Records that the follower has acknowledged at least `committed_index` from the leader's
committed prefix. This is used for commit-group awareness and follower commit tracking.

### Preconditions
- `committed_index` is a valid log index
- The WF invariant holds

### Postconditions
- `committed_index' = max(committed_index_old, committed_index)` — monotonically non-decreasing
- All other fields unchanged
- WF invariant preserved (trivially — only `committed_index` changes)

### Edge Cases
- Calling with the same value: idempotent (no change)
- Calling with a smaller value: no change (strict `>` guard in the Rust code)

### Inferred Intent
Monotonicity is the only safety property here. The field tracks the highest
committed index the follower has confirmed, used for determining when a commit
can be acknowledged to a group even if some replicas lag.

---

## `maybe_decr_to(rejected: u64, match_hint: u64, request_snapshot: u64) → bool`

### Purpose
Called when the leader receives a rejection (MsgAppendResponse with `reject = true`).
Decides whether to retreat `next_idx` and by how much, or to ignore the rejection as stale.

The function branches on `self.state`:

### In `Replicate` State

**Stale rejection** (return `false`, no change) if:
- `rejected < matched` — the rejection is for an old entry already confirmed replicated, OR
- `rejected == matched && request_snapshot == INVALID_INDEX` — duplicate or no-op rejection

**Active rejection** (return `true`) if not stale:
- If `request_snapshot == INVALID_INDEX`: set `next_idx = matched + 1` (reset to known good boundary)
- Otherwise: set `pending_request_snapshot = request_snapshot` (follower needs a snapshot)

### In `Probe` (or `Snapshot`) State

**Stale rejection** (return `false`, no change) if:
- `(next_idx == 0 || next_idx - 1 != rejected) && request_snapshot == INVALID_INDEX`
  — the rejection is not for the most recently sent index

**Active rejection** (return `true`) if not stale:
- If `request_snapshot == INVALID_INDEX`:
  - `next_idx = max(matched + 1, min(rejected, match_hint + 1))`
  - Clear `paused` (resume probing)
- If `pending_request_snapshot == INVALID_INDEX`:
  - Set `pending_request_snapshot = request_snapshot`
  - Clear `paused`
- Otherwise: just clear `paused`

### Postconditions (both states)

- `matched` is **never changed** by `maybe_decr_to`
- `committed_index` is **never changed** by `maybe_decr_to`
- WF invariant preserved:
  - Replicate success (no snap): `next_idx' = matched + 1 ≥ matched + 1` ✓
  - Probe success (no snap): `next_idx' = max(matched+1, ...) ≥ matched + 1` ✓
  - All failure paths: state unchanged

### Edge Cases
- `rejected < matched`: always stale in Replicate state
- `next_idx = 1, rejected = 0`: in Probe, `next_idx - 1 = 0 = rejected` → not stale
- `match_hint = 0`: in Probe no-snap case, `min(rejected, 1)` clamps next_idx to 1 at minimum

### Inferred Intent
`maybe_decr_to` implements Raft's log backtracking heuristic. The stale-rejection check
prevents a slow follower's old rejection message from needlessly rewinding a faster
leader's progress. The `matched + 1` floor in both states ensures WF is preserved.

---

## Open Questions

1. **WF of `next_idx = 0` path**: The Rust code checks `self.next_idx == 0` as a special
   case in the Probe branch. Is `next_idx = 0` actually reachable? In practice it should
   not be (because `new()` starts with `next_idx ≥ 1`), but the defensive check suggests
   it has been a concern. **Maintainer input welcome.**

2. **`update_committed` vs. committed in `RaftLog`**: How does `Progress::committed_index`
   relate to `RaftLog::committed`? Is it always ≤? **Architectural clarification welcome.**

3. **`commit_group_id`**: The `commit_group_id` field affects quorum calculations elsewhere.
   Is `update_committed` the only way it advances? **Maintainer input welcome.**

---

*🔬 Lean Squad — automated formal specification. Generated from source analysis.*
