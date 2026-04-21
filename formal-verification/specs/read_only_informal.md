# Informal Specification: `ReadOnly` — ReadIndex Linearisability Bookkeeping

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Target**: `ReadOnly` struct and its five methods  
**Source**: `src/read_only.rs`  
**Lean file**: `formal-verification/lean/FVSquad/ReadOnly.lean` (Phase 4: 12 theorems, 11 proved)

---

## Purpose

`ReadOnly` implements leader-side bookkeeping for the Raft **ReadIndex** linearisability
protocol (Raft §6.4 / etcd raft). When a client issues a read-only query, the leader must
confirm it is still the current leader before serving the read. The protocol proceeds in
three steps:

1. **Register the request** (`add_request`): the leader captures its current commit index
   and records the request in a FIFO queue alongside the commit index. The self-ID is the
   initial acknowledger (the leader counts itself as a heartbeat acknowledgement).
2. **Await a quorum of heartbeat acknowledgements** (`recv_ack`): when follower nodes
   respond to the broadcast heartbeat, the leader records each acknowledgement in the
   corresponding status entry.
3. **Deliver ready requests** (`advance`): once a quorum of acks is observed (by the
   caller, not tracked inside `ReadOnly`), the leader calls `advance` with the context
   that reached quorum. `advance` dequeues that entry and all earlier ones (FIFO prefix
   semantics) and returns their captured commit indices for response delivery.

The two auxiliary methods `last_pending_request_ctx` and `pending_read_count` expose
queue state for diagnostic and flow-control purposes.

---

## Data Structures

### `ReadIndexStatus`

Represents one pending read-only request:

- `req : Message` — the original read-only request message (context bytes, sender info).
  *In the Lean model this field is elided; only `index` and `acks` are kept.*
- `index : u64` — the commit index at the time the request was registered. The response
  must be delivered at or after this index.
- `acks : HashSet<u64>` — the set of node IDs that have acknowledged the leader's
  heartbeat for this request.
  *In the Lean model, `acks` is a `List Nat` (ordered, possibly with duplicates if the
  dedup invariant is not separately tracked).*

### `ReadOnly`

Container for all pending read-only requests:

- `option : ReadOnlyOption` — `Safe` (default, quorum-based) or `LeaseBased` (clock-based).
  *In the Lean model, this field is omitted — it only affects the call site, not the data
  structure invariants.*
- `pending_read_index : HashMap<Vec<u8>, ReadIndexStatus>` — maps context bytes to status.
  *In the Lean model: `pending : List (Nat × ReadIndexStatus)` — an association list.*
- `read_index_queue : VecDeque<Vec<u8>>` — FIFO queue of context keys, in insertion order.
  *In the Lean model: `queue : List Nat`.*

**Key representation difference**: the Rust uses a `HashMap` (unordered by key) plus a
`VecDeque` (ordered FIFO). The Lean model unifies these into a `List (Nat × ReadIndexStatus)`
for `pending` plus `List Nat` for `queue`, which is simpler to reason about but loses the
O(1) lookup of the HashMap.

---

## Invariants

### QueuePendingInv (Key Invariant)

At all times, the set of context keys in `queue` equals the set of keys in `pending`:

```
∀ ctx ∈ queue, amember ctx pending = true
∀ (ctx, _) ∈ pending, ctx ∈ queue
```

This is established by the empty state and preserved by every operation.

### NoDuplicates (Implicit Invariant)

No context key appears twice in `queue`. This is maintained because `add_request` is
idempotent: if the context is already present it is a no-op. This invariant is required
to prove RO8 (`advance` removes exactly the right entries). It is **not yet formally
stated** in the Lean model (RO8 has one remaining `sorry`).

### AckSetMonotonicity

Once a node ID is in the `acks` set for a context, it remains there. `recv_ack` only adds
to `acks`, never removes. (This is implicit in the Lean model — `recvAck` uses set-insert
semantics.)

---

## Method Specifications

### `add_request(index, req, self_id)`

**Precondition**: None (always safe to call; idempotent on duplicate context).

**Behaviour**:
- Let `ctx = req.entries[0].data` (the request's context bytes).
- If `ctx` is already in `pending_read_index`: return immediately (idempotent guard).
- Otherwise:
  - Create `ReadIndexStatus { req, index, acks: {self_id} }`.
  - Insert into `pending_read_index` with key `ctx`.
  - Push `ctx` to the back of `read_index_queue`.

**Postconditions**:
- If `ctx` was absent: `pending_read_index[ctx] = { index, acks: {self_id} }` and
  `ctx` is at the back of `read_index_queue`.
- `pending_read_index.len() = old_len + 1` and `read_index_queue.len() = old_queue_len + 1`.
- `QueuePendingInv` is preserved.
- If `ctx` was present: state is unchanged.

**Edge cases**:
- Calling `add_request` twice with the same `ctx` but different `index` or `req`:
  the second call is silently ignored. The first `index` is the one used for linearisability.

---

### `recv_ack(id, ctx) -> Option<&HashSet<u64>>`

**Precondition**: None (gracefully handles absent `ctx`).

**Behaviour**:
- Look up `ctx` in `pending_read_index`.
- If not found: return `None`.
- If found: insert `id` into `acks`; return `Some(&acks)` (after insertion).

**Postconditions**:
- Returns `None` iff `ctx ∉ pending_read_index`.
- Returns `Some(acks')` where `acks' = old_acks ∪ {id}`.
- `id ∈ acks'` always holds when `Some` is returned.
- All prior acks are preserved: `old_acks ⊆ acks'`.
- Only `acks` changes; `index` and `req` are unchanged.
- `queue` is unchanged.

**Edge cases**:
- `recv_ack` is idempotent: calling it twice with the same `(id, ctx)` leaves `acks`
  unchanged on the second call.
- Acks are accumulative and never removed.

---

### `advance(ctx, logger) -> Vec<ReadIndexStatus>`

**Precondition**: `ctx ∈ read_index_queue`. If this precondition is violated, the Rust
code calls `fatal!(logger, ...)` which is a panic. The Lean model treats the violation
as a no-op (returns empty and leaves state unchanged), omitting the panic.

**Behaviour**:
- Find the position `i` of `ctx` in `read_index_queue` (linear scan from front).
- If not found: return `[]` (no-op in the Lean model; panic in Rust).
- If found at position `i`:
  - Dequeue the first `i + 1` entries from `read_index_queue` (indices 0..=i).
  - Remove their corresponding entries from `pending_read_index`.
  - Return the `ReadIndexStatus` values in queue order (front to back).

**Postconditions**:
- The returned list has length `i + 1` where `i` is the 0-based position of `ctx` in the queue.
- The returned statuses are in insertion order (FIFO).
- `ctx ∉ new_queue` (the context that triggered the advance is removed).
- All contexts that were behind `ctx` in the queue (after position `i`) remain in `queue` and `pending`.
- `QueuePendingInv` is preserved.
- `pending_read_count` decreases by `i + 1`.

**FIFO delivery guarantee**: `advance` delivers entries in the order they were registered
(oldest first). This is essential for linearisability: reads registered earlier are
delivered with their earlier commit indices.

**Edge cases**:
- `advance` on the very first entry (`i = 0`): returns a single-element list.
- `advance` on the last entry (i = queue.len()-1): empties both `queue` and `pending`.
- Multiple `advance` calls: each call removes a prefix, subsequent calls see the remaining suffix.

---

### `last_pending_request_ctx() -> Option<Vec<u8>>`

**Behaviour**: Returns the context of the most-recently-added pending request (the back of
`read_index_queue`), or `None` if the queue is empty.

**Postconditions**:
- Returns `None` iff `read_index_queue` is empty.
- Returns `Some(ctx)` where `ctx` is the last element of `read_index_queue`.
- State is not modified.

**Use case**: The leader uses this to attach the most recent pending read context to the
next heartbeat broadcast, so followers' acks can be matched to all pending contexts (including
earlier ones in the queue, which are advanced when the last one is ready).

---

### `pending_read_count() -> usize`

**Behaviour**: Returns `read_index_queue.len()`.

**Postconditions**:
- Returns 0 iff `read_index_queue` is empty.
- By `QueuePendingInv`, equals `pending_read_index.len()` as well.
- State is not modified.

---

## Key Properties (Driving Lean Theorems)

| Property | Status | Lean theorem |
|----------|--------|--------------|
| `add_request` is idempotent when ctx present | ✅ Proved | `RO1_addRequest_idempotent` |
| `add_request` extends queue when ctx absent | ✅ Proved | `RO2_addRequest_extends_queue` |
| `add_request` extends pending when ctx absent | ✅ Proved | `RO3_addRequest_extends_pending` |
| Added entry is retrievable with correct ack set | ✅ Proved | `RO4_addRequest_entry_present` |
| `recvAck` returns `none` iff ctx absent | ✅ Proved | `RO5_recvAck_none_iff_absent` |
| `recvAck` adds id to ack set | ✅ Proved | `RO6_recvAck_adds_id` |
| `advance` is a no-op when ctx absent | ✅ Proved | `RO7_advance_noop_if_absent` |
| `advance` removes ctx from queue | 🔄 1 sorry | `RO8_advance_removes_ctx` (needs NoDuplicates) |
| Empty state satisfies `QueuePendingInv` | ✅ Proved | `RO9_inv_empty` |
| `add_request` preserves `QueuePendingInv` | ✅ Proved | `RO10_inv_add` |
| `add_request` increments `pendingReadCount` | ✅ Proved | `RO11_addRequest_count` |
| `pendingReadCount = 0 ↔ queue empty` | ✅ Proved | `RO12_pendingReadCount_zero_iff` |

---

## Approximations / Omissions

| Aspect | Rust | Lean model |
|--------|------|------------|
| Context keys | `Vec<u8>` (arbitrary bytes) | `Nat` |
| Request payload | `req: Message` in `ReadIndexStatus` | Elided (only `index` and `acks` kept) |
| Ack set | `HashSet<u64>` (no duplicates, O(1)) | `List Nat` (may have duplicates if id already present guard not formalized) |
| Map | `HashMap<Vec<u8>, ReadIndexStatus>` (O(1) lookup) | Association list `List (Nat × ReadIndexStatus)` (O(n) lookup) |
| Queue | `VecDeque<Vec<u8>>` | `List Nat` |
| `ReadOnlyOption` | `Safe` / `LeaseBased` | Omitted |
| Panic path | `fatal!(logger, ...)` in `advance` if ctx not found | Returns no-op in Lean model |
| Logger | `&Logger` parameter | Omitted |
| `acks` dedup | HashSet guarantees no duplicates | List: `recvAck` guards against duplicate ids, but no formal NoDuplicates invariant yet |

---

## Open Questions

1. **NoDuplicates invariant for acks**: The Lean `acks` field is a `List Nat`. `recvAck` guards against adding a duplicate id, but there is no formal proof that `acks` never contains duplicates. This is needed to prove `RO8`. Should we add `NoDuplicates acks` as an additional invariant to the `ReadIndexStatus`?

2. **NoDuplicates for queue**: The Lean `queue` is a `List Nat`. `add_request` is idempotent but there is no formal proof of no-duplicates for `queue`. This is also needed for `RO8` — specifically, `List.take (i+1)` must include `ctx` exactly once.

3. **advance-then-add round-trip**: After `advance ctx`, can `ctx` be re-registered with `add_request`? The spec should say yes (the Lean `#guard` test confirms this). This is a correctness question about client-side behaviour.

4. **Quorum check location**: The quorum check (`acks.len() >= quorum`) is done by the caller (in `raft.rs`), not inside `ReadOnly`. The `ReadOnly` spec correctly models `recv_ack` as returning the ack set for the caller to inspect — but the formal property "acks ≥ quorum implies advance is correct" is not stated here. This could be a future theorem connecting `ReadOnly` to `HasQuorum`.
