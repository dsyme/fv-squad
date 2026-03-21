# Informal Specification: `UncommittedState` Tracker

**Source**: `src/raft.rs`
**Rust type**: `struct UncommittedState` with methods `maybe_increase_uncommitted_size` and `maybe_reduce_uncommitted_size`

🔬 *Lean Squad — automated formal verification for dsyme/fv-squad.*

---

## Purpose

`UncommittedState` tracks the total byte size of uncommitted log entries on a **leader** node.
The Raft protocol allows a leader to bound the amount of data it proposes before receiving
acknowledgements, preventing the leader from overwhelming followers with unbounded writes.

Two operations are provided:

- **`maybe_increase_uncommitted_size(ents)`**: called when a leader is about to propose new
  entries. It checks whether adding `ents` would exceed `max_uncommitted_size`. If not, it
  atomically adds the size and returns `true` (accepted). Otherwise it leaves the size unchanged
  and returns `false` (rejected).

- **`maybe_reduce_uncommitted_size(ents)`**: called when entries are committed/applied. It
  subtracts the size of the committed entries (skipping those from before this node became leader)
  from the tracked total, returning `true` normally. Returns `false` (with a warning) if the
  computed reduction would underflow (i.e., the tracked size would go negative), in which case
  the size is clamped to 0.

Together they maintain `uncommitted_size` as an approximate upper bound on the byte volume of
unacknowledged proposals outstanding from this leader.

---

## Preconditions

None: both methods are callable on any `UncommittedState` value. They do not panic.

### Fields

| Field | Type | Semantics |
|-------|------|-----------|
| `max_uncommitted_size` | `usize` | Maximum allowed total byte size. `NO_LIMIT = u64::MAX` means unlimited. |
| `uncommitted_size` | `usize` | Current tracked total byte size of uncommitted entries. |
| `last_log_tail_index` | `u64` | The last log index at the moment this node became leader. Entries at or before this index are skipped when reducing (they belong to the prior leader's tenure). |

---

## `maybe_increase_uncommitted_size(ents)` Specification

### Inputs
- `ents`: a slice of log entries; each has an associated data byte length.

### Semantics

Let `size = sum of ent.get_data().len() for ent in ents` (the total data byte size of the proposed entries).

**Fast path**: if `is_no_limit()` (i.e., `max_uncommitted_size == NO_LIMIT`), return `true` without
modifying state. (No limit is enforced.)

**Otherwise**:

The proposal is accepted (returns `true`, `uncommitted_size += size`) iff **any** of:
1. `size == 0`: empty entries (e.g., leader-election no-ops) are always accepted.
2. `uncommitted_size == 0`: the queue is currently empty — always accept at least one entry.
3. `size + uncommitted_size <= max_uncommitted_size`: adding the entries stays within budget.

If none of the above hold, the proposal is **rejected** (returns `false`, state unchanged).

### Postconditions (when `is_no_limit()` is false)

- Returns `true` iff: `size = 0 ∨ uncommitted_size = 0 ∨ size + uncommitted_size ≤ max_uncommitted_size`
- Returns `true` → `new_uncommitted_size = old_uncommitted_size + size`
- Returns `false` → `new_uncommitted_size = old_uncommitted_size` (no change)
- Returns `true` → `new_uncommitted_size ≤ max_uncommitted_size` (budget satisfied)
  - *Except*: when `old_uncommitted_size = 0`, any size (even > max) is accepted; in this case
    `new_uncommitted_size = size` which may exceed `max_uncommitted_size`.
    This implements the "at least one entry" guarantee.

### Key Invariant

> **Budget invariant**: If the previous call increased uncommitted_size from a non-zero state,
> then `uncommitted_size ≤ max_uncommitted_size` after the increase.

The one-entry exception (case 2 above) means that when `uncommitted_size` transitions from 0 to
non-zero, the new size may exceed `max_uncommitted_size`. This is intentional: the leader must
always be able to propose at least one entry.

---

## `maybe_reduce_uncommitted_size(ents)` Specification

### Inputs
- `ents`: a slice of committed entries to deduct from the tracking.

### Semantics

**Fast paths**:
- If `is_no_limit()`: return `true`, no state change.
- If `ents.is_empty()`: return `true`, no state change.

**Otherwise**:

The entries from `ents` that were proposed during *this leader's tenure* are the ones with
`index > last_log_tail_index`. These are "charged" to the current uncommitted size. Entries
at or before `last_log_tail_index` came from a prior term and should not be counted.

Let `size = sum of ent.get_data().len() for ent in ents where ent.index > last_log_tail_index`.

(Note: the implementation uses `skip_while(ent.index <= last_log_tail_index)`, which requires
the entries to be sorted by index — a condition guaranteed by the Raft log.)

**Underflow guard**:
- If `size > uncommitted_size`: clamp to 0, return `false`. (Underflow: the tracked size
  was less than the amount being released. This indicates an accounting inaccuracy, typically
  from entries committed before this node became leader being counted twice.)
- Otherwise: `new_uncommitted_size = old_uncommitted_size - size`, return `true`.

### Postconditions

- Returns `false` iff `size > uncommitted_size` (underflow)
- Returns `false` → `new_uncommitted_size = 0`
- Returns `true` → `new_uncommitted_size = old_uncommitted_size - size`
- `new_uncommitted_size ≤ old_uncommitted_size` (non-increasing)
- `new_uncommitted_size = 0` iff (`returns false` ∨ `size = uncommitted_size`)

---

## Invariants (derived properties)

Let `S = uncommitted_size`, `M = max_uncommitted_size`, `L = last_log_tail_index`.

1. **Non-negativity**: `S ≥ 0` always (since `usize` is unsigned; the underflow guard in
   `maybe_reduce` prevents wrap-around by clamping to 0).

2. **Budget-on-increase**: after `maybe_increase` returns `true` from state `S > 0`:
   `S_new ≤ M`.

3. **Monotone-decrease**: `maybe_reduce` never increases `S`.

4. **Commutativity of nil**: `maybe_increase([]) = true` and `maybe_increase` is a no-op
   for entries with data size 0 — well, it does add 0 to `S`, but `S_new = S`.

5. **Sequence property**: `maybe_increase(A) = true; maybe_reduce(A)` produces the same
   state as no-op, provided all entries in `A` have `index > L`.

---

## Edge Cases

1. **`is_no_limit()`** (`max_uncommitted_size == NO_LIMIT`): both functions return `true`
   immediately; `uncommitted_size` is never updated. The field is essentially ignored.

2. **Empty entries**: `maybe_increase([])` always returns `true` (size = 0). This is fine:
   no-op proposals (zero-size entries like leader elections) are always allowed.

3. **`uncommitted_size = 0` at time of increase**: any batch of entries is accepted, even if
   `size > max_uncommitted_size`. This is the "minimum-one-entry" guarantee.

4. **`last_log_tail_index` filtering**: if all entries in `ents` have `index ≤ last_log_tail_index`,
   then `size = 0` and `maybe_reduce` returns `true` with no state change. The entries are
   treated as pre-leadership and not charged.

5. **Underflow in `maybe_reduce`**: if `size > uncommitted_size`, the function logs a warning,
   sets `uncommitted_size = 0`, and returns `false`. This can happen when applying a `Ready` that
   was generated before this node became leader (and the old `uncommitted_size` did not account for
   all the entries being committed). The implementation considers this "not a big problem in most
   situations."

6. **`max_uncommitted_size = 0`**: this is treated as "0 bytes max". Every batch with nonzero
   total size from a non-empty state (`S > 0`) will be rejected unless `S = 0` (the one-entry
   guarantee). In practice, `max_uncommitted_size` is set to `NO_LIMIT` (u64::MAX) by default.

---

## Examples

**Normal increase** (`S = 100, M = 1000, L = 5`):
```
entries = [data=50, index=6], size = 50
size + S = 150 ≤ 1000 → accept; S_new = 150; returns true
```

**Rejection** (`S = 900, M = 1000, L = 5`):
```
entries = [data=200, index=6], size = 200
S > 0 ∧ 200 + 900 = 1100 > 1000 → reject; S unchanged = 900; returns false
```

**One-entry guarantee** (`S = 0, M = 100, L = 5`):
```
entries = [data=500, index=6], size = 500
S = 0 → accept regardless; S_new = 500; returns true (even though 500 > 100)
```

**Normal reduce** (`S = 150, L = 5`):
```
entries = [data=50, index=6]
index=6 > L=5 → charged; size = 50
50 ≤ 150 → S_new = 100; returns true
```

**Pre-leader entries filtered in reduce** (`S = 150, L = 10`):
```
entries = [data=50, index=7], index=7 ≤ L=10 → skipped; size = 0
size = 0 → fast path returns true, S unchanged = 150
```

**Underflow in reduce** (`S = 20, L = 5`):
```
entries = [data=50, index=6], size = 50
50 > 20 → underflow; S_new = 0; returns false
```

---

## Inferred Intent

`UncommittedState` is a flow-control mechanism: it prevents a Raft leader from filling up
follower log buffers and memory with unbounded uncommitted proposals. The counter tracks
an *approximation* of outstanding bytes, not an exact accounting. The "at least one entry"
guarantee ensures liveness: a leader can always make progress even at the size limit.

The `last_log_tail_index` filter exists to handle **leader transitions**: when a node becomes
leader, it may commit entries from the previous leader's term (as a Raft safety mechanism).
These should not be charged against the new leader's uncommitted budget, since the new leader
did not propose them.

The underflow return value (`false`) is informational: the Raft implementation logs a warning
but continues operating. The approximation error is bounded: it can only make the effective
limit *more permissive* than intended (since `uncommitted_size` is clamped to 0 rather than
going below 0).

---

## Open Questions

1. **Q: Is `last_log_tail_index` reset when a leader steps down and re-elected?**
   If yes, the skip-while logic is correct across multiple leader tenures. If not, old entries
   from a previous tenure might be double-skipped.

2. **Q: Can `uncommitted_size` exceed `max_uncommitted_size` due to the one-entry guarantee?**
   Yes, when `S = 0` before increase. Is this tracked / compensated for elsewhere?

3. **Q: Is there a proof that `reduce ∘ increase` is a near-identity?**
   For entries with `index > last_log_tail_index` and data size `sz`, `increase([sz])` adds
   `sz` and `reduce([sz])` subtracts `sz` — composing to a no-op. Is this invariant relied on?

4. **Q: What happens if entries in `ents` for `maybe_reduce` are not sorted by index?**
   The `skip_while` assumes sorted order. If entries are unsorted, the skip may miss some entries.
   This is likely always true in practice (Raft log appends are in order) but is not checked.

---

## Key Propositions for Lean Formalisation

```
-- Acceptance condition
theorem increase_true_iff (s : UncommittedState) (size : Nat) (hnoLimit : ¬s.isNoLimit) :
  (maybeIncrease s size).2 = true ↔
  (size = 0 ∨ s.uncommittedSize = 0 ∨ size + s.uncommittedSize ≤ s.maxUncommittedSize)

-- Rejection is non-mutating
theorem increase_false_unchanged (s : UncommittedState) (size : Nat)
    (h : (maybeIncrease s size).2 = false) :
  (maybeIncrease s size).1.uncommittedSize = s.uncommittedSize

-- Budget invariant after non-trivial acceptance
theorem increase_budget (s : UncommittedState) (size : Nat)
    (hnoLimit : ¬s.isNoLimit) (hS : s.uncommittedSize > 0)
    (h : (maybeIncrease s size).2 = true) :
  (maybeIncrease s size).1.uncommittedSize ≤ s.maxUncommittedSize

-- Reduce is monotone-decreasing
theorem reduce_monotone (s : UncommittedState) (size : Nat) :
  (maybeReduce s size).1.uncommittedSize ≤ s.uncommittedSize

-- Underflow clamping
theorem reduce_underflow (s : UncommittedState) (size : Nat)
    (h : size > s.uncommittedSize) :
  (maybeReduce s size).1.uncommittedSize = 0 ∧ (maybeReduce s size).2 = false

-- Round-trip: increase then reduce recovers state (non-underflow case)
theorem increase_reduce_roundtrip (s : UncommittedState) (size : Nat)
    (hnoLimit : ¬s.isNoLimit)
    (hAccept : (maybeIncrease s size).2 = true) :
  let s' := (maybeIncrease s size).1
  (maybeReduce s' size).1.uncommittedSize = s.uncommittedSize

-- No-limit fast path
theorem increase_noLimit (s : UncommittedState) (size : Nat) (h : s.isNoLimit) :
  (maybeIncrease s size).2 = true ∧ (maybeIncrease s size).1 = s

theorem reduce_noLimit (s : UncommittedState) (size : Nat) (h : s.isNoLimit) :
  (maybeReduce s size).2 = true ∧ (maybeReduce s size).1 = s
```
