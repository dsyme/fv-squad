# Informal Specification: `limit_size`

> **File**: `src/util.rs` — `pub fn limit_size<T: PbMessage + Clone>(entries: &mut Vec<T>, max: Option<u64>)`
>
> 🔬 *Lean Squad — informal specification extracted for Task 2 (Informal Spec Extraction).*

---

## Purpose

`limit_size` enforces a byte-size budget on a list of Protobuf-encoded log entries. It
**in-place truncates** the list to the longest prefix whose total serialised byte-size fits
within `max`, subject to a **minimum-one guarantee**: the result always contains at least
one entry (even if that entry alone exceeds the budget).

This is used by `RaftLog::slice` and `Storage::entries` to cap the volume of log entries
returned in a single call, preventing unbounded allocations when a follower is far behind.

---

## Preconditions

| # | Condition | Note |
|---|-----------|------|
| P1 | `entries` is any `Vec<T>` (including empty) | No constraint on initial length |
| P2 | `max` is either `None`, `Some(NO_LIMIT)` (= `u64::MAX`), or `Some(limit)` for a finite limit | |
| P3 | `T: PbMessage + Clone` — `compute_size()` returns `u32` (never overflows a `u64` accumulator for any realistic entry count) | ⚠️ Open question: can accumulated `size` overflow `u64`? See §Open Questions. |

---

## Postconditions

Let `n = entries.len()` (before the call) and `size(e)` denote `e.compute_size()` (as `u64`).

| Case | Postcondition |
|------|---------------|
| **C1** `n ≤ 1` (0 or 1 entries) | `entries` is unchanged |
| **C2** `max = None` or `max = Some(NO_LIMIT)` | `entries` is unchanged |
| **C3** `max = Some(limit)`, `n ≥ 2` | `entries` is truncated to a prefix of the original (see §Prefix Behaviour) |

### Prefix Behaviour (Case C3)

Let `prefix_size(k) = size(entries[0]) + size(entries[1]) + ... + size(entries[k-1])`, i.e.
the cumulative byte size of the first `k` entries.

Define `limit_count` as the output length. Then:

- **Minimum**: `limit_count ≥ 1` — the result always contains at least one entry.
- **Prefix**: the result is `entries[0..limit_count]` — a prefix of the original list.
- **Size-respecting**: `prefix_size(limit_count) ≤ limit` (the total fits in the budget),
  **OR** `limit_count = 1` (single-entry exception: the first entry is always kept even if
  `size(entries[0]) > limit`).
- **Maximality**: for any `k` with `1 < k ≤ n`, if `prefix_size(k) ≤ limit` then `k ≤ limit_count`.
  Equivalently: if the output was truncated (i.e., `limit_count < n`), then adding one more
  entry would exceed the budget: `prefix_size(limit_count + 1) > limit`.

### Concise characterisation

```
limit_count = max { k ∈ [1, n] | k = 1 ∨ prefix_size(k) ≤ limit }
```

Or equivalently, `limit_count` is the result of taking entries one by one until the running
total first exceeds `limit`, always keeping at least one.

---

## Invariants / Algorithm Behaviour

The implementation uses a `take_while` iterator with a running `size` accumulator:

1. The **first entry is always taken** (special case: when `size == 0`, the entry is accepted
   unconditionally and its size is accumulated).
2. Each subsequent entry is accepted iff `cumulative_size + size(entry) ≤ limit`.
3. The accumulated count is used to `truncate` the vector.

This means:
- If `size(entries[0]) > limit`, the result still has length 1 (the first entry alone).
- The decision is made on the **cumulative size including** the current entry (not excluding).

---

## Edge Cases

| Scenario | Expected behaviour |
|----------|--------------------|
| Empty `entries` (`n = 0`) | No change (early return for `n ≤ 1`) |
| Single entry (`n = 1`) | No change (early return for `n ≤ 1`) |
| `max = None` | No change |
| `max = Some(u64::MAX)` (= `NO_LIMIT`) | No change |
| `max = Some(0)` | Result has exactly 1 entry (first entry kept unconditionally) |
| All entries have `compute_size() = 0` | Result is unchanged (all entries accepted; sum is 0 ≤ limit for any limit) |
| First entry alone exceeds limit | Result has exactly 1 entry |
| All entries fit within limit | Result is unchanged |

---

## Inferred Intent

- The single-entry minimum is a deliberate design choice ensuring Raft progress: a follower
  must be able to receive at least one entry in every `AppendEntries` RPC, otherwise
  replication would stall. An empty entries slice would be interpreted as "no new entries"
  and make no progress.
- `NO_LIMIT = u64::MAX` is used as a sentinel so callers can pass an `Option<u64>` with
  `NO_LIMIT` meaning "no budget restriction", distinct from `None` (which has the same
  semantic here: unlimited).
- The function modifies in place to avoid an extra allocation.

---

## Examples (from documentation)

```rust
// template: each entry ~100 bytes
let mut entries = vec![t, t, t, t, t];  // 5 entries
limit_size(&mut entries, Some(220));
assert_eq!(entries.len(), 2);
// prefix_size(1) = 100 ≤ 220 ✓
// prefix_size(2) = 200 ≤ 220 ✓
// prefix_size(3) = 300 > 220 ✗  →  truncate at 2
```

```rust
limit_size(&mut entries, Some(0));
assert_eq!(entries.len(), 1);
// max = 0: even size(entries[0]) > 0, but first entry always kept
```

---

## Lean 4 Modelling Notes

- **Type abstraction**: model entries as `List Nat` where each `Nat` represents the byte size
  of one entry (i.e., the "payload" is abstracted to just its size).
- **`compute_size` abstraction**: replace `T.compute_size()` with a given pure function
  `size : Fin n → Nat` (or equivalently, model `entries` as `List Nat` directly).
- **`NO_LIMIT`**: in Lean, model this as `max : Option Nat` where `None` means unlimited.
  This avoids the `u64::MAX` sentinel. The `NO_LIMIT` sentinel and `None` can be unified.
- **In-place mutation**: model as a pure function `limitSize : List Nat → Option Nat → List Nat`
  returning the truncated prefix. The mutable-in-place semantics is irrelevant to correctness.
- **Key properties to verify**:
  - `limitSize l max` is a prefix of `l`
  - `(limitSize l max).length ≥ min 1 l.length`
  - `(limitSize l max).sum ≤ max` (when max is finite and result has > 1 element)
  - Maximality: the next entry (if any) would exceed the budget
  - `decide`-checkable for small instances

---

## Open Questions

1. **Overflow safety**: `size` is declared `u64` and accumulates `e.compute_size()` (a `u32`).
   For very large entry lists, could `size` overflow `u64`? Raft log entries are at most
   a few MB each, so with `u64` and realistic entry counts this is not exploitable — but
   it is worth stating as an explicit approximation in the Lean model.
2. **Semantics of `compute_size()`**: is it deterministic and pure? (Assumed yes, since
   Protobuf serialisation is deterministic for a given message.)
3. **`NO_LIMIT` vs `None`**: are they treated identically everywhere? (Currently yes in this
   function, but callers may distinguish them.)
