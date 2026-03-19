# Inflights — Informal Specification

Informal specification for the `Inflights` ring buffer from `src/tracker/inflights.rs`.

🔬 *Lean Squad — auto-extracted informal specification.*

---

## Purpose

`Inflights` is a **bounded FIFO queue** that tracks the Raft log indices of in-flight
`MsgAppend` messages sent to a single peer. It is used by the Raft progress tracker to
enforce a cap on the number of unacknowledged messages per peer, preventing the sender
from flooding a slow or partitioned follower.

The queue stores monotonically increasing `u64` log indices. When a batch of entries is
acknowledged (via `free_to`), all indices **≤ to** are removed from the front of the queue.
The `cap` field bounds the maximum occupancy.

---

## Preconditions

- `cap > 0` is expected for meaningful use (a zero-capacity buffer is always full).
- `add` must only be called when `full()` returns `false`; calling it on a full buffer
  panics in Rust.

---

## Postconditions and Operation Semantics

### `new(cap) → Inflights`
- Returns an empty buffer with the given capacity.
- **Post**: `count = 0`, `start = 0`, `cap = cap`.

### `full(&self) → bool`
- **Returns** `true` iff the queue is at capacity (`count == cap`), OR if an
  `incoming_cap` reduction is pending and `count >= incoming_cap`.
- **No side effects.**

### `add(&mut self, inflight: u64)`
- **Pre**: `!full()`.
- Appends `inflight` to the logical end of the queue.
- **Post**: `count` increases by 1; `inflight` appears at logical position `count - 1`.
- The underlying ring buffer slot `(start + count - 1) % cap` holds `inflight`.

### `free_to(&mut self, to: u64)`
- Removes all elements from the **front** of the queue whose value is **≤ to**.
- Stops at the first element **> to**.
- **No-op** if the queue is empty or if `buffer[start] > to`.
- **Post**: `count` decreases by the number of freed entries; `start` advances accordingly.
- **Key property**: all remaining entries are strictly **> to**.
- If freeing empties the queue and a pending capacity resize (`incoming_cap`) exists,
  the resize takes effect immediately.

### `free_first_one(&mut self)`
- Frees exactly the oldest (front) element.
- Equivalent to `free_to(buffer[start])` when non-empty.
- **No-op** if empty.

### `reset(&mut self)`
- Empties the queue entirely; `count = 0`, `start = 0`.
- Applies any pending `incoming_cap` resize.

### `set_cap(&mut self, incoming_cap: usize)`
- Adjusts the capacity. Three sub-cases:
  - Equal to current: no-op.
  - Larger: resize buffer (re-linearise if the ring wraps around past `cap`).
  - Smaller: if queue is empty, apply immediately; otherwise, store as `incoming_cap`
    and apply lazily when the queue next drains.

---

## Invariants

**INV-1 (bounded)**: `count ≤ cap` at all times.

**INV-2 (start in range)**: `start < cap` when `cap > 0` (or `start = 0` when empty
and unallocated).

**INV-3 (ring addressing)**: For `i ∈ [0, count)`, the logical entry at position `i` is
stored at `buffer[(start + i) % cap]`.

**INV-4 (non-decreasing values)**: In practice the Raft protocol appends indices in
strictly increasing order, so the queue contents are always strictly increasing. The
implementation does not enforce this, but correct Raft usage guarantees it. This means
`free_to` always frees a contiguous prefix.

---

## Edge Cases

- **Empty queue**: `free_to` and `free_first_one` are no-ops.
- **`free_to` with `to < buffer[start]`**: no entries freed (left-of-window check).
- **`free_to` that empties the queue**: pending `incoming_cap` is applied.
- **`set_cap` smaller while busy**: deferred via `incoming_cap`; `full()` accounts for
  the pending reduction.
- **Wrap-around**: when `start + count ≥ cap`, the next `add` writes to
  `(start + count) % cap` (the beginning of the buffer). This is the core ring buffer
  behaviour; it is transparent to callers.

---

## Examples

```
cap = 10, start = 0, count = 0:  []
add(0..4):                         [0, 1, 2, 3, 4]  (start=0, count=5)
add(5..9):                         [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]  (count=10, full)
free_to(4):                        [5, 6, 7, 8, 9]   (start=5, count=5)
add(10):                           [5..9, 10]         (start=5, count=6)
free_to(8):                        [9, 10]            (start=9, count=2, wraps)
add(11..13):                       [9..13]            (start=9, count=5)
free_to(12):                       [13]               (start=3, count=1, wrapped around)
```

---

## Inferred Intent

The name "inflights" mirrors the TCP congestion window concept: the queue holds
unacknowledged messages, and `free_to` advances the acknowledgment pointer. The ring
buffer avoids repeated memory allocation while maintaining O(1) amortised enqueue/dequeue.

The `incoming_cap` mechanism supports online resizing of the Raft replication window
without disrupting in-flight messages: shrinks are deferred until the current wave drains.

---

## Open Questions

1. **Monotonicity of values**: should `add` assert that `inflight > buffer[(start + count - 1) % cap]`
   (i.e., strictly increasing)? The code does not, but Raft usage is always monotone.
   **Lean spec note**: the abstract model should state this as a precondition on `add` if
   we want to leverage INV-4 in proofs.

2. **`set_cap` and `full()`**: when `incoming_cap` is set, `full()` checks
   `count >= incoming_cap` rather than `count == cap`. Is this exactly right for the
   interim state? The tests in `test_inflights_set_cap` confirm it but the interaction
   is subtle.

3. **`free_to` stability**: if values are *not* monotone, `free_to` might free a
   non-contiguous prefix. The implementation's linear scan always frees a prefix up to
   the first entry `> to`, which is correct regardless of monotonicity.
