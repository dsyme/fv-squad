# Informal Specification: `Inflights` Ring Buffer

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

**Source**: `src/tracker/inflights.rs`  
**Purpose**: Flow-control buffer that tracks in-flight Raft messages to a single peer.

---

## Purpose

`Inflights` is a bounded FIFO buffer of *in-flight message indices* (log indices
of messages sent but not yet acknowledged by a follower).  It prevents a leader
from sending more than `cap` messages at once to any single peer.

The buffer is implemented as a ring buffer internally for efficiency, but its
**abstract observable behaviour** is that of an ordered sequence of `u64` values,
where elements are appended to the back (`add`) and freed from the front
(`free_to`, `free_first_one`).

In practice the caller always adds entries in non-decreasing order (increasing
log indices), so the sequence is **sorted non-decreasingly** at all times.  This
sortedness is a key invariant that makes `free_to` correct.

---

## Abstract Model

Abstractly, an `Inflights` object is:

```
Inflights = { queue : List u64, cap : usize }
```

* `queue`: the ordered sequence of in-flight message indices (oldest first).
* `cap`: the maximum number of simultaneous in-flight messages allowed.

The concrete ring-buffer state (`start`, `count`, `buffer`, `incoming_cap`) is
an implementation detail; only `queue` and `cap` are exposed by the spec.

---

## Operations

### `new(cap) → Inflights`

**Precondition**: none.  
**Postcondition**: `queue = []`, `cap = cap`.

### `full() → bool`

**Returns**: `true` iff the buffer is at capacity.  
**Postcondition**: `full() = (queue.len() == cap)`.

> *Note*: `incoming_cap` introduces a secondary fullness condition (see Open
> Questions), but in the principal model we ignore it.

### `add(inflight: u64)`

**Precondition**: `!full()`, i.e., `queue.len() < cap`.  
**Postcondition**: `queue' = queue ++ [inflight]`, `cap' = cap`.  
**Effect**: appends `inflight` to the back.  
**Panics** when called on a full buffer (precondition violation).

### `free_to(to: u64)`

**Precondition**: none (no-op if already empty or `to` is before the window).  
**Postcondition**: `queue' = queue.drop_while(|x| x ≤ to)`.  
That is, all entries at the **front** of the queue that are ≤ `to` are removed;
entries stop being removed at the first entry **strictly greater than** `to`.  
**Effect**: acknowledges all in-flight messages with index ≤ `to`.  
`count' ≤ count`.

> **Important**: `free_to` removes the longest **prefix** of the queue whose
> elements are ≤ `to`.  It does **not** remove later elements that might also be
> ≤ `to`; however, since in practice the queue is sorted, there are no such
> later elements.

### `free_first_one()`

**Precondition**: none (no-op if empty).  
**Postcondition**: equivalent to `free_to(queue[0])` when the queue is non-empty.  
**Effect**: frees the oldest in-flight message.

### `reset()`

**Precondition**: none.  
**Postcondition**: `queue' = []`.  Also applies any pending `incoming_cap`.  
**Effect**: discards all in-flight tracking.

---

## Invariants

| ID | Invariant | Description |
|----|-----------|-------------|
| INV1 | `count ≤ cap` | Buffer never exceeds capacity (enforced by `add` precondition). |
| INV2 | Sorted non-decreasing | Raft adds entries in index order; queue is always sorted. |
| INV3 | Non-negative | All entries are non-negative (`u64 ≥ 0`). |

---

## Key Properties

| ID | Property | Statement |
|----|----------|-----------|
| P1 | `add` increments count | `(add x).count = count + 1` |
| P2 | `add` appends | `(add x).queue = queue ++ [x]` |
| P3 | `add` is safe below cap | `count < cap → (add x).count ≤ cap` |
| P4 | `free_to` result head > `to` | If `(freeTo to).queue` is non-empty, its head is `> to` |
| P5 | `free_to` drops prefix ≤ `to` | `(freeTo to).queue = queue.dropWhile (· ≤ to)` |
| P6 | Under sortedness: all freed ≤ `to` | If sorted, then every element that was removed was ≤ `to` |
| P7 | Under sortedness: all remaining > `to` | If sorted, every element in the result is `> to` |
| P8 | `free_to` is monotone in count | `(freeTo to).count ≤ count` |
| P9 | `free_to` preserves sortedness | If sorted before, sorted after |
| P10 | `freeFirstOne` = `freeTo(head)` | When non-empty: `freeFirstOne = freeTo(queue[0])` |
| P11 | `reset` clears | `reset.count = 0` |

---

## Preconditions

| Operation | Precondition |
|-----------|-------------|
| `add(x)` | `!full()` (count < cap) |
| `free_to(to)` | none (safe to call on empty) |
| `free_first_one()` | none (no-op on empty) |
| `reset()` | none |
| `full()` | none |

---

## Edge Cases

* **Empty buffer, `free_to(to)`**: returns immediately without modifying state.
* **`free_to(to)` where `to < queue[0]`**: no elements removed (prefix is empty).
* **`free_to(to)` where `to ≥ queue[last]`**: all elements removed.
* **`free_first_one` on empty queue**: no-op.
* **`add` on full buffer**: panic (precondition violation, not modelled in spec).
* **Sorted queue with wrap-around**: the ring buffer may wrap around in the
  underlying array, but the abstract queue order is maintained.

---

## Examples (from tests)

**Test `test_inflight_add`**:
```
new(10) → queue=[], cap=10
add(0..5) → queue=[0,1,2,3,4]
add(5..10) → queue=[0,1,2,3,4,5,6,7,8,9]
```

**Test `test_inflight_free_to`**:
```
new(10), add(0..10) → queue=[0..9]
free_to(4) → queue=[5,6,7,8,9]   -- drops 0,1,2,3,4
free_to(8) → queue=[9]           -- drops 5,6,7,8
add(10..15) → queue=[9,10,11,12,13,14]
free_to(12) → queue=[13,14]      -- drops 9,10,11,12
free_to(14) → queue=[]           -- drops 13,14
```

**Test `test_inflight_free_first_one`**:
```
new(10), add(0..10) → queue=[0..9]
free_first_one() → free_to(0) → queue=[1,2,3,4,5,6,7,8,9]
```

---

## Inferred Intent

The `Inflights` structure is a **sliding window** over acknowledged log indices.
It enforces an upper bound on *concurrent* in-flight messages per peer.  The
primary correctness requirement is:

1. **Safety** (`count ≤ cap`): prevents overloading a slow follower.
2. **Progress** (`free_to` actually removes acknowledged entries): ensures the
   window advances and the leader can send new messages.
3. **Correctness of `free_to`** (under sortedness): the freed entries are
   exactly those with index ≤ `to`, not more and not fewer (given sorted input).

---

## Open Questions

1. **`incoming_cap`**: the `set_cap` / `incoming_cap` mechanism allows dynamic
   capacity changes. When `incoming_cap` is pending, `full()` additionally
   returns true if `count >= incoming_cap`. This secondary condition is not
   modelled in the primary spec above. Should the formal spec include capacity
   change semantics?

2. **Sortedness as invariant or precondition?**: the spec states sortedness as
   an invariant (maintained by correct usage). Should it be formally enforced
   by typing (e.g., `SortedList`), or left as an assumed precondition on `free_to`?

3. **`u64::MAX` treatment**: in a `u64`-only model, integer overflow is absent.
   Does the spec need to handle wraparound? (In the Rust code, indices are
   `u64` and in practice never reach `u64::MAX`.)
