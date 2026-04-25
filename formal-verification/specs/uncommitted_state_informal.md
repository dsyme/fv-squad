# Informal Specification: `UncommittedState`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: `src/raft.rs` — struct `UncommittedState` and its `impl` block.  
**Phase**: 2 — Informal Specification.

---

## Purpose

`UncommittedState` implements **flow control** for a Raft leader: it tracks the
total byte-size of log entries that have been proposed but not yet committed, and
enforces an optional upper bound (`max_uncommitted_size`) on that total.

When the limit is reached, new proposals are rejected (the cluster is "back-pressured"),
preventing unbounded memory growth on the leader.  A value of `max_uncommitted_size = 0`
means "no limit" (the `NO_LIMIT` sentinel).

The struct is only maintained on the **leader node**; on followers, `uncommitted_size`
has no defined semantics.  The `last_log_tail_index` field records the last log index
at the moment the node became leader; entries at or below that index are excluded from
size accounting in `maybe_reduce` (they belong to a prior leader's term).

---

## Fields

| Field | Type | Meaning |
|-------|------|---------|
| `max_uncommitted_size` | `usize` | Maximum total byte-size of uncommitted entries; 0 = NO_LIMIT |
| `uncommitted_size` | `usize` | Current total byte-size of uncommitted entries |
| `last_log_tail_index` | `u64` | Last log index at time of becoming leader; entries ≤ this are ignored in reduce |

---

## Preconditions

- `uncommitted_size` is always ≤ `max_uncommitted_size` (when `!is_no_limit()`), as
  enforced by the invariant that `maybe_increase` returns `false` rather than violating it.
- Entries passed to `maybe_reduce` are a prefix of entries previously accepted by
  `maybe_increase` (they are applied entries from the Raft `Ready`).

---

## `is_no_limit()`

**Returns**: `true` iff `max_uncommitted_size == 0`.  
**Effect**: no state change.

When true, all size checks are bypassed: `maybe_increase` always returns `true` and
`maybe_reduce` always returns `true`.

---

## `maybe_increase_uncommitted_size(ents: &[Entry]) -> bool`

**Purpose**: Try to account for the additional uncommitted bytes represented by `ents`.
Returns `true` if accounting succeeded (entries are allowed), `false` if rejected.

**Computation**:
```
size = sum of ent.data.len() for ent in ents
```

**Allowed (returns `true`) iff one of**:
1. `is_no_limit()` — no limit, always allow.
2. `size == 0` — empty payload entries (e.g., leader election no-ops) are always allowed.
3. `uncommitted_size == 0` — at least one entry must always be admitted (prevents starvation
   when even a single entry exceeds the limit).
4. `size + uncommitted_size ≤ max_uncommitted_size` — within budget.

**Effect when allowed**: `uncommitted_size += size`.  
**Effect when rejected**: no state change.

**Key invariant preserved**: if `!is_no_limit()` and we were at `uncommitted_size ≤ max` before,
we remain at `uncommitted_size ≤ max` after (cases 1–4 are the only paths that mutate).

---

## `maybe_reduce_uncommitted_size(ents: &[Entry]) -> bool`

**Purpose**: Account for entries that have been applied/committed, reducing the
uncommitted byte counter.

**Returns `true` immediately (no-op) if**:
- `is_no_limit()`, or
- `ents` is empty.

**Computation**:
```
size = sum of ent.data.len() for ent in ents where ent.index > last_log_tail_index
```
(Entries at or below `last_log_tail_index` were proposed before this node became leader
and are excluded from accounting.)

**Then**:
- If `size > uncommitted_size`: set `uncommitted_size = 0`, return `false`.
  (This handles the case where the user advances a `Ready` from before becoming leader;
  the size over-count is harmlessly saturated to zero.)
- Else: `uncommitted_size -= size`, return `true`.

**Postcondition**: `uncommitted_size` is non-negative (never wraps below zero).

---

## Invariants

**INV1 — Bounded**: if `!is_no_limit()`, then `uncommitted_size ≤ max_uncommitted_size`
at all times.  This is preserved by `maybe_increase` (which rejects violations) and by
`maybe_reduce` (which only decreases `uncommitted_size`).

**INV2 — Monotone increase gate**: `maybe_increase` returns `false` only when it would
violate INV1 (i.e., `size + uncommitted_size > max_uncommitted_size` and none of the
exception clauses fire).

**INV3 — Saturating reduce**: `maybe_reduce` never decreases `uncommitted_size` below 0;
it saturates at 0 and returns `false` to signal the anomalous case.

---

## Edge Cases

| Scenario | Behaviour |
|----------|-----------|
| `max_uncommitted_size = 0` (no limit) | All operations return `true`, `uncommitted_size` tracks total but limit is never enforced |
| `ents` is empty in `maybe_increase` | `size = 0`, always returns `true` (case 2) |
| Single entry > max | Allowed only when `uncommitted_size == 0` (case 3 — starvation prevention) |
| `ents` is empty in `maybe_reduce` | Returns `true` immediately (fast path) |
| Entries from before becoming leader | Filtered by `last_log_tail_index`; filtered entries contribute 0 to `size` |
| `size > uncommitted_size` in reduce | Saturates to 0, returns `false` |
| Repeated `maybe_reduce` with same entries | Second call may see `uncommitted_size = 0`, returns `false` |

---

## Examples

**Example 1 — basic flow**:
- State: `{ max=100, uncommitted=0, tail=0 }`
- `maybe_increase([30B, 40B])` → `true`, `uncommitted=70`
- `maybe_increase([40B])` → `false` (70+40=110 > 100), `uncommitted=70`
- `maybe_reduce([30B, 40B])` → `true`, `uncommitted=0`

**Example 2 — starvation prevention**:
- State: `{ max=10, uncommitted=0, tail=0 }`
- `maybe_increase([50B])` → `true` (uncommitted_size==0 exception), `uncommitted=50`

**Example 3 — no limit**:
- State: `{ max=0, uncommitted=0, tail=0 }`
- `maybe_increase([9999B])` → `true`, `uncommitted=9999`
- `maybe_reduce([9999B])` → `true`, `uncommitted=0`

**Example 4 — reduce with pre-leader entries**:
- State: `{ max=100, uncommitted=30, tail=5 }`
- `maybe_reduce([ent@3(20B), ent@6(10B)])` → entry@3 filtered (3 ≤ 5), size=10; `uncommitted=20`, returns `true`

---

## Inferred Intent

The `uncommitted_size == 0` exception in `maybe_increase` is a deliberate
**starvation-prevention** mechanism: a leader with a full buffer must still accept at
least one new entry, otherwise a single large proposal could permanently stall the cluster.
This is documented in the source comments as "we should allow at least one uncommitted entry."

The `false` return from `maybe_reduce` is a **signal** to the caller that accounting was
anomalous (entries from before becoming leader were included in the `Ready`). It is not
an error; `uncommitted_size` is correctly set to 0 in this case.

---

## Open Questions

1. **Is `INV1` invariant actively asserted?** The code relies on `maybe_increase`
   returning `false` to prevent violations; is there any explicit assertion or test
   confirming `uncommitted_size ≤ max_uncommitted_size` holds at all times?

2. **Double-advance safety**: If a user accidentally calls `maybe_reduce` twice with
   the same entries, the second call sees `uncommitted_size` already reduced, may return
   `false` and saturate to 0. Is this a correctness concern or handled by the caller?

3. **What resets `last_log_tail_index`?** It is set when a node becomes leader; when
   does it become stale or get reset?
