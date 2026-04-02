# Informal Specification: `Progress` — Raft Follower Replication State Machine

> 🔬 *Lean Squad — automated formal verification for this repository.*

**Source**: `src/tracker/progress.rs`, `src/tracker/state.rs`

---

## Purpose

`Progress` tracks the replication state of a single Raft follower as observed by the leader.
It is a **state machine** with three states (`Probe`, `Replicate`, `Snapshot`) and a small set
of mutations that drive the leader's decisions about what to send next and whether to send at all.

The two most important fields are:
- `matched`: the highest log index confirmed replicated on the follower (0 if unknown).
- `next_idx`: the next log index the leader will send to this follower.

---

## State Machine

### States

| State | Meaning |
|-------|---------|
| `Probe` | Leader is not sure of follower's log. Sends at most one message per heartbeat. |
| `Replicate` | Follower is in sync. Leader optimistically advances `next_idx` on each send. |
| `Snapshot` | A snapshot is in flight. No log entries are sent until snapshot is acknowledged. |

The **default** state (for newly created `Progress`) is `Probe`.

### Legal Transitions

```
Probe ──become_replicate──▶ Replicate ──become_probe──▶ Probe
Probe ──become_snapshot──▶  Snapshot  ──become_probe──▶ Probe
Replicate ──become_snapshot──▶ Snapshot
```

There is no direct transition from `Snapshot` to `Replicate`. After a snapshot succeeds,
the follower transitions to `Probe`, and then to `Replicate` once it proves it is up to date.

---

## Key Invariant

**`matched + 1 ≤ next_idx`** (written `wf` in the formal spec)

After any well-formed operation starting from a well-formed `Progress`, the invariant is
preserved. `new(next_idx, ...)` requires `next_idx ≥ 1` to satisfy the invariant initially
(since `matched` starts at 0).

---

## Field Semantics

| Field | When used | Meaning |
|-------|-----------|---------|
| `matched` | always | Highest confirmed-replicated index (0 = unknown) |
| `next_idx` | always | Next index to send |
| `state` | always | Current state |
| `paused` | `Probe` only | If true, suppress messages until a heartbeat |
| `pending_snapshot` | `Snapshot` only | Index of the in-flight snapshot |
| `pending_request_snapshot` | any | Non-zero if follower explicitly requested a snapshot |
| `recent_active` | always | Whether follower has communicated recently |
| `ins` | `Replicate` only | Sliding window of in-flight log indices |

---

## Preconditions

### `new(next_idx, ins_size)`
- `next_idx ≥ 1`: constructing a progress with next_idx = 0 would immediately violate the
  invariant (`matched = 0`, `next_idx = 0`).

### `become_snapshot(snapshot_idx)`
- Callers should ensure `snapshot_idx > matched`; otherwise the snapshot is not advancing
  the follower's state.  *(The code does not assert this.)*

### `maybe_update(n)`
- No precondition beyond a well-formed `Progress`.

### `maybe_decr_to(rejected, match_hint, request_snapshot)`
- No precondition; stale messages are silently rejected and `false` is returned.

---

## Postconditions

### `become_probe()`
- `state = Probe`
- `paused = false`, `pending_snapshot = 0`
- If prior state was `Snapshot`: `next_idx = max(matched + 1, pending_snapshot_old + 1)`
- Otherwise: `next_idx = matched + 1`
- `matched` **unchanged**

### `become_replicate()`
- `state = Replicate`
- `paused = false`, `pending_snapshot = 0`
- `next_idx = matched + 1`
- `matched` **unchanged**

### `become_snapshot(snapshot_idx)`
- `state = Snapshot`
- `paused = false`, `pending_snapshot = snapshot_idx`
- `matched`, `next_idx` **unchanged**

### `maybe_update(n)` → `(updated : bool)`
- If `n > matched`:
  - `updated = true`
  - `matched = n`
  - `next_idx = max(old_next_idx, n + 1)`
  - `paused = false` (resume)
- If `n ≤ matched`:
  - `updated = false`
  - `matched` unchanged
  - `next_idx = max(old_next_idx, n + 1)` *(next_idx still advances)*
  - `paused` unchanged

### `maybe_decr_to(rejected, match_hint, request_snapshot)` → `(decremented : bool)`
- **Replicate state**:
  - Returns `false` (stale) if `rejected < matched` or (`rejected = matched` and no snapshot requested)
  - Returns `true` and sets `next_idx = matched + 1` if no snapshot request
  - Returns `true` and sets `pending_request_snapshot = request_snapshot` if snapshot requested
- **Probe / Snapshot state**:
  - Returns `false` (stale) if `next_idx - 1 ≠ rejected` (and no snapshot request)
  - Returns `true` and sets `next_idx = max(matched+1, min(rejected, match_hint+1))` if no snapshot request
  - Returns `true` and sets `pending_request_snapshot = request_snapshot` if snapshot requested (and PRS was INVALID)
  - Always calls `resume()` when returning `true`

### `is_paused()`
- `Probe` state: returns `paused`
- `Replicate` state: returns `ins.full()`
- `Snapshot` state: returns `true` (always paused)

### `is_snapshot_caught_up()`
- Returns `true` iff `state = Snapshot ∧ matched ≥ pending_snapshot`

---

## Invariants

1. **wf**: `matched + 1 ≤ next_idx`
   - Established by `new(next_idx)` when `next_idx ≥ 1`.
   - Preserved by all state transitions listed above.
   - **Not** preserved by arbitrary field writes; the type's fields are `pub` in Rust.

2. **snapshot_state**: When `state = Snapshot`, `pending_snapshot > 0` (set by `become_snapshot`).
   - Exception: `snapshot_failure()` resets `pending_snapshot = 0` while state remains `Snapshot`.
   - This means after `snapshot_failure()`, `is_snapshot_caught_up()` returns `true` whenever `matched ≥ 0`, which is always true! This triggers the transition to Probe. This behaviour appears intentional.

3. **ins invariant** (modelled externally): In `Replicate` state, `ins` holds the indices of in-flight messages.

---

## Edge Cases

1. **`next_idx = 0`**: Not permitted by the `wf` invariant; `maybe_decr_to` handles the `next_idx == 0` case specially (Rust: check for overflow before `next_idx - 1`).

2. **`matched = 0`**: Valid initial state. `maybe_update(0)` returns `false` since `0 < 0` is false.

3. **`become_probe` from `Snapshot` with `pending_snapshot = 0`**: Happens after `snapshot_failure()`. The new `next_idx = max(matched+1, 0+1) = max(matched+1, 1)`. If `matched = 0`, next_idx = 1. OK.

4. **Overflow**: The Rust code uses `u64`. Properties in the Lean model use `Nat` (unbounded), abstracting away overflow. For practical log sizes, `Nat` is equivalent.

---

## Examples

| Operation | Before | After |
|-----------|--------|-------|
| `new(5)` | — | matched=0, next=5, Probe, unpaused |
| `become_replicate()` | matched=3, Probe | matched=3, next=4, Replicate |
| `become_snapshot(10)` | matched=3, Replicate | matched=3, next=4, Snapshot, pending=10 |
| `become_probe()` from Snapshot(10) | matched=3, Snapshot(10) | matched=3, next=11, Probe |
| `become_probe()` from Snapshot(0) | matched=3, Snapshot(0) | matched=3, next=4, Probe |
| `maybe_update(7)` | matched=3, next=5 | matched=7, next=8, return true |
| `maybe_update(2)` | matched=3, next=5 | matched=3, next=5, return false |
| `maybe_update(4)` | matched=3, next=5 | matched=3, next=5, return false *(next stays 5 since 5 ≥ 4+1)* |

---

## Inferred Intent

The `Progress` state machine implements the optimistic replication strategy in Raft:
- `Probe` is the conservative mode (slow follower or just started).
- `Replicate` is the fast mode — the leader sends entries without waiting for ACKs,
  trusting the inflight window to keep things bounded.
- `Snapshot` is the recovery mode — the follower is so far behind that a full snapshot
  is needed.

The invariant `matched + 1 ≤ next_idx` ensures the leader never tries to send an index
it already knows the follower has. `maybe_decr_to` walks `next_idx` backwards when
rejections arrive, but never below `matched + 1`.

---

## Open Questions

1. **After `become_snapshot`**, should `next_idx` be advanced to `snapshot_idx + 1`?
   The code does not do this; it leaves `next_idx` at its current value. During Snapshot
   state the index isn't used for log sending, so this is probably harmless — but it means
   the invariant `matched + 1 ≤ next_idx` may need to be qualified as
   "holds only in non-Snapshot state" or "is not violated by become_snapshot if it held before".
   *(Actually: become_snapshot does not change `matched` or `next_idx`, so if the invariant
   held before the call, it holds after.)*

2. **`snapshot_failure()` sets `pending_snapshot = 0`** while remaining in Snapshot state.
   Is the subsequent `is_snapshot_caught_up()` returning `true` (for matched ≥ 0, i.e., always)
   intentional? It seems to be the mechanism by which a failed snapshot triggers a transition
   back to Probe via the caller. Worth a maintainer comment.

3. **`INVALID_INDEX = 0`** is also a valid log index for some purposes. Is `pending_request_snapshot = 0`
   always safe as the "not pending" sentinel, given log indices start from 0? The code seems
   to treat `0` as INVALID everywhere for snapshot indices.
