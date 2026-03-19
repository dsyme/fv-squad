# Informal Specification — `Progress` Replication Tracker

> 🔬 *Lean Squad — informal specification for `src/tracker/progress.rs`.*

## Purpose

`Progress` tracks the Raft leader's view of one follower's replication state.
It records how far the follower has caught up (`matched`), what index to send
next (`next_idx`), which replication mode the follower is in (`state`), and
whether sending is currently paused.

The leader uses this to decide whether to send entries, how many to send, and
when to advance the commit index.

---

## State Machine

`Progress` is a state machine with three states:

```
        reset / election
           ┌──────────────────────────────────────────────┐
           │                                              │
       ┌───▼───┐  become_replicate   ┌────────────┐       │
       │ Probe │────────────────────►│ Replicate  │       │
       └───┬───┘◄──── become_probe ──└────────────┘       │
           │                                              │
           │ become_snapshot    ┌──────────┐              │
           └───────────────────►│ Snapshot │──────────────┘
                                └──────────┘
                                  become_probe
```

- **Probe**: Leader sends one message per heartbeat interval to probe the
  follower's log position. If no reply, pauses until next heartbeat.
- **Replicate**: Optimistic fast-path replication. Leader pipelines entries up
  to the in-flight cap.
- **Snapshot**: A snapshot is in progress. All replication is paused until the
  snapshot is confirmed applied.

---

## Fields

| Field | Type | Meaning |
|-------|------|---------|
| `matched` | `u64` | Highest log index confirmed acknowledged by the follower |
| `next_idx` | `u64` | Next log index to send to the follower |
| `state` | `ProgressState` | Current replication mode |
| `paused` | `bool` | Whether sending is paused (Probe mode only) |
| `pending_snapshot` | `u64` | The snapshot index being sent (Snapshot mode only) |

---

## Representation Invariant

**INV-1 (index ordering)**: `matched + 1 ≤ next_idx`

The "next" index to send is always strictly beyond what has been matched.
This invariant must hold after every operation.

*Inferred from*: `become_probe` sets `next_idx = max(matched+1, ...)`,
`become_replicate` sets `next_idx = matched+1`, `maybe_update` only advances
both fields in a consistent manner.

---

## Operations

### `maybe_update(n) → bool`

**Purpose**: Process an acknowledgement of log entries up to index `n`.

**Semantics**:
1. If `n > matched`: update is needed.
   - Set `matched = n`, `resume()` (clears `paused`).
   - If `next_idx < n + 1`: advance `next_idx = n + 1`.
   - Return `true`.
2. If `n ≤ matched`: stale acknowledgement, no change.
   - Return `false`.

**Postconditions**:
- `(matched, next_idx)` after = `(max(old.matched, n), max(old.next_idx, n+1))`
- Returns `true` iff `n > old.matched`
- If returns `true`, `paused = false`
- `valid` invariant is preserved

**Edge cases**:
- `n = 0`: always returns `false` since `matched ≥ 0`.
- Multiple calls with decreasing `n`: only first matters.

### `become_probe()`

**Purpose**: Transition to Probe state. Called after a rejection or snapshot
completion.

**Semantics**:
- If in Snapshot state: set `next_idx = max(matched+1, pending_snapshot+1)`
  (must be beyond the snapshot to avoid re-sending it).
- Otherwise: set `next_idx = matched + 1`.
- Set `state = Probe`, `paused = false`, `pending_snapshot = 0`.

**Postconditions**:
- `state = Probe`
- `paused = false`
- `valid` invariant holds: `matched + 1 ≤ next_idx`

### `become_replicate()`

**Purpose**: Transition to Replicate state. Called when the follower has caught
up enough to start pipelined replication.

**Semantics**:
- Set `state = Replicate`, `paused = false`, `pending_snapshot = 0`.
- Set `next_idx = matched + 1`.

**Postconditions**:
- `state = Replicate`
- `next_idx = matched + 1`
- `valid` holds

### `become_snapshot(snapshot_idx)`

**Purpose**: Transition to Snapshot state. Called when the follower is so far
behind that a snapshot must be sent.

**Semantics**:
- Set `state = Snapshot`, `paused = false`, `pending_snapshot = snapshot_idx`.
- Does NOT change `matched` or `next_idx`.

**Postconditions**:
- `state = Snapshot`
- `pending_snapshot = snapshot_idx`
- Always paused (any message in Snapshot state is blocked)

### `maybe_decr_to(rejected, match_hint) → bool`

**Purpose**: Respond to a log rejection (the follower's log diverges from what
the leader thought).

**Semantics (simplified, ignoring request_snapshot path)**:
- If Replicate state:
  - If `rejected ≤ matched`: stale rejection, ignore, return `false`.
  - Otherwise: roll back `next_idx = matched + 1`, return `true`.
- If Probe state:
  - If `next_idx - 1 ≠ rejected`: stale rejection, ignore, return `false`.
  - Otherwise: set `next_idx = max(min(rejected, match_hint+1), matched+1)`.
    Resumes (clears paused), returns `true`.

**Key property**: Never decreases `next_idx` below `matched + 1`.

---

## Invariants

1. **INV-1**: `matched + 1 ≤ next_idx` — always holds.
2. **INV-2**: In Snapshot state, `paused = false` (the `is_paused` check handles
   this differently — Snapshot always blocks by definition, so `paused` field is
   irrelevant).
3. **INV-3**: `pending_snapshot > 0` only when `state = Snapshot`.
   (Inferred; not enforced by code — `pending_snapshot` is set to 0 on every
   non-snapshot transition.)

---

## Examples

### `maybe_update` advancing matched and next_idx

```
Before: matched=5, next_idx=7
maybe_update(8) → true
After:  matched=8, next_idx=9
```

### `maybe_update` with n=next_idx-1 (partial fill)

```
Before: matched=5, next_idx=10
maybe_update(7) → true
After:  matched=7, next_idx=10  (next_idx unchanged, already ≥ n+1)
```

### State transition from Snapshot back to Probe

```
Before: state=Snapshot, matched=3, pending_snapshot=10
become_probe()
After:  state=Probe, matched=3, next_idx=11  (= max(4, 11))
```

---

## Open Questions

1. **INVALID_INDEX handling**: `pending_request_snapshot` and the
   `request_snapshot` parameter of `maybe_decr_to` are set to `INVALID_INDEX`
   (a sentinel value) in various paths. The exact semantics of this sentinel
   are not modelled here. Should the spec include it?
2. **`update_committed`**: Is there an invariant relating `committed_index` to
   `matched`? The code only requires `committed_index` increases monotonically.
3. **`ins` (Inflights)**: The in-flight message tracker affects `is_paused` in
   Replicate state. This spec ignores Inflights for simplicity — should the spec
   capture the pausing behaviour in Replicate mode?
4. **INV-3 strictness**: Is `pending_snapshot > 0` actually an invariant, or
   can `become_snapshot(0)` legitimately be called?

---

## Inferred Intent

The `Progress` struct is the leader's per-follower *window* into the replication
pipeline. The three-state model ensures the leader uses the right protocol for
each situation:
- **Probe**: the safe fallback when the follower's state is unknown.
- **Replicate**: the fast path when the follower is in sync.
- **Snapshot**: the recovery path when the log has been compacted past the follower.

The central correctness property is **INV-1**: `matched + 1 ≤ next_idx`. If this
were violated (`next_idx ≤ matched`), the leader might think it has already sent
entries that are confirmed — but then re-send them with a lower index, breaking
log consistency.
