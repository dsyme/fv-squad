# Informal Specification — `ReadOnly` Queue

> 🔬 *Lean Squad — informal specification for `src/read_only.rs`.*

## Purpose

The `ReadOnly` struct in `raft-rs` manages linearisable **read-only requests** under
the `ReadIndex` protocol. When a client issues a read-only request, the leader must
confirm that it is still the current leader by obtaining heartbeat acknowledgements
from a quorum of peers before serving the read. `ReadOnly` tracks the in-flight
requests, their associated commit indices, and the set of heartbeat acknowledgements
collected so far.

The three core operations are:

| Operation | Description |
|-----------|-------------|
| `add_request(index, req, self_id)` | Enqueue a new read-only request with commit index `index`, including `self_id` in the initial ack set. Idempotent if the context key is already pending. |
| `recv_ack(id, ctx)` | Record that peer `id` has acknowledged the heartbeat for context `ctx`. Returns the updated ack set (or `None` if `ctx` is unknown). |
| `advance(ctx)` | Complete all requests up to and including `ctx` in queue order: dequeue them and return their statuses. No-op if `ctx` is not in the queue. |

Additionally:

- `last_pending_request_ctx()` — returns the context key at the back of the queue (None if empty).
- `pending_read_count()` — returns the number of pending requests.

---

## Preconditions

- **`add_request(index, req, self_id)`**: `req.entries` must have at least one entry
  (the context key is `req.entries[0].data`). If the extracted key is already in
  `pending_read_index`, the function returns immediately without modification.
- **`recv_ack(id, ctx)`**: No hard precondition; if `ctx` is absent, the function is
  a no-op and returns `None`.
- **`advance(ctx)`**: If `ctx` is not in the queue, the function returns an empty
  vector and makes no state changes. The function expects `ctx` to appear in
  `read_index_queue` whenever it is in `pending_read_index` (invariant).

---

## Postconditions

### `add_request(index, req, self_id)` — `ctx = req.entries[0].data`

1. **Idempotent**: if `ctx ∈ pending_read_index` before the call, all fields are unchanged.
2. **Insertion**: if `ctx ∉ pending_read_index`, then after the call:
   - `ctx ∈ pending_read_index` with `ReadIndexStatus { req, index, acks: {self_id} }`.
   - `ctx` is appended to the **back** of `read_index_queue`.
   - All other entries in `pending_read_index` and `read_index_queue` are unchanged.

### `recv_ack(id, ctx)`

1. If `ctx ∈ pending_read_index`: `id` is inserted into `pending_read_index[ctx].acks`;
   the function returns `Some(&updated_acks)`.
2. If `ctx ∉ pending_read_index`: state is unchanged; returns `None`.
3. In either case, `read_index_queue` is unchanged.

### `advance(ctx)`

1. If `ctx ∉ read_index_queue`: state is unchanged; returns `[]`.
2. If `ctx` is at position `i` in `read_index_queue` (0-indexed):
   - Returns the statuses for `read_index_queue[0..=i]` in queue order.
   - Removes those `i+1` entries from both `read_index_queue` and `pending_read_index`.
   - All entries after position `i` in the queue are unaffected.

---

## Invariants

The following invariants should hold after any sequence of valid operations:

1. **Queue = Pending Keys** (INV-1): `read_index_queue` contains exactly the keys
   present in `pending_read_index`, in the order they were inserted.
2. **No Duplicates** (INV-2): `read_index_queue` has no duplicate entries.
   (Ensured by the early-return check in `add_request`.)
3. **Self-Ack** (INV-3): For every pending request, `self_id ∈ acks`. (Established by
   `add_request` and not changed by subsequent operations.)
4. **Prefix Invariant** (INV-4): `advance(ctx)` returns a **prefix** of the queue, not
   an arbitrary subset.

---

## Edge Cases

- **Empty queue**: `last_pending_request_ctx()` returns `None`; `pending_read_count()` returns 0.
- **Single pending request**: `advance(ctx)` returns the one entry and leaves the queue empty.
- **`advance` with unknown ctx**: returns `[]`; queue and pending map are both unchanged.
- **Duplicate `add_request`**: the second call for the same ctx is silently ignored.
  Acks accumulated by earlier `recv_ack` calls are preserved.
- **`recv_ack` with unknown ctx**: returns `None`; no state change.
- **Advancing past the last element**: leaves the queue empty.

---

## Examples

```
State: queue = [A, B, C], pending = {A: acks={1}, B: acks={1}, C: acks={1}}

add_request(10, msgA2, 1)  → no-op (A already pending)
recv_ack(2, B)             → acks[B] = {1, 2};  returns Some({1,2})
advance(B)                 → returns [statusA, statusB]; queue = [C]; pending = {C: ...}
advance(X)                 → returns []; queue = [C]; no change
```

---

## Inferred Intent

The `ReadOnly` module implements a **FIFO confirmation queue** for the Raft ReadIndex
protocol (§6.4 of the Raft thesis). Requests are served in queue order — once a
heartbeat round is complete, `advance` drains all requests that can now be answered.
The idempotency check in `add_request` ensures that retried or duplicated requests do
not corrupt the queue or create spurious entries in the pending map.

---

## Open Questions

- Is it guaranteed that `ctx` keys are globally unique across clients? The code trusts
  callers to use unique byte strings (e.g., request UUIDs), but this is not enforced
  inside the module.
- Is `recv_ack` ever called before the corresponding `add_request`? The code silently
  ignores it (`None` return), but the intent is that heartbeats always reference
  previously-added requests.
