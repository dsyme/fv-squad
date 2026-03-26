# Informal Specification: `limit_size`

> 🔬 *Lean Squad — automated formal verification for this repository.*

**Source file**: `src/util.rs`  
**Function signature**: `pub fn limit_size<T: PbMessage + Clone>(entries: &mut Vec<T>, max: Option<u64>)`  
**FV phase**: 2 (Informal Spec)

---

## Purpose

`limit_size` truncates a mutable vector of protobuf-encoded entries so that the total serialised byte-size of the retained entries does not exceed a given maximum. The function always preserves at least one entry regardless of size — this is a deliberate policy choice to guarantee callers always get at least one entry back even if the budget is exceeded by a single item.

---

## Preconditions

1. `entries` may be empty or non-empty.
2. `max` is either:
   - `None` — meaning no limit
   - `Some(u64::MAX)` — equivalent to no limit (`NO_LIMIT` constant)
   - `Some(n)` for any other `n ≥ 0` — a byte budget

---

## Postconditions

Let `orig` be the original vector and `result` be the post-call vector.

1. **Prefix**: `result` is a prefix of `orig`. Specifically, `result == orig[0..k]` for some `0 ≤ k ≤ |orig|`.

2. **Non-empty preservation**: If `|orig| ≥ 1`, then `|result| ≥ 1`.
   - Equivalently: the result always contains at least the first entry.

3. **No-op when ≤ 1 entry**: If `|orig| ≤ 1`, the vector is unmodified.

4. **No-op when unlimited**:
   - If `max = None`, `result == orig`.
   - If `max = Some(u64::MAX)`, `result == orig`.

5. **Size bound**: If `max = Some(n)` with `n < u64::MAX`:
   - Either `|result| = 1` (forced minimum), **or** the total serialised size of all entries in `result` satisfies `Σ compute_size(e) ≤ n`.

6. **Maximality** (greedy): The result is the *longest* prefix of `orig` satisfying the size bound. Formally: if `result == orig[0..k]` and `k < |orig|`, then adding `orig[k]` would exceed the budget:
   - `Σ_{i=0}^{k} compute_size(orig[i]) > n`

7. **Truncation only**: The function only truncates — it never reorders, modifies, or inserts entries.

---

## Invariants

- The first entry of the original vector is always retained (when the vector was non-empty).
- The size accumulation is prefix-monotone: if entry `i` is included, then all entries `0..i` are included.

---

## Edge Cases

| Input | Expected behaviour |
|-------|--------------------|
| `entries = []`, any `max` | Vector unchanged (empty). |
| `entries = [e]`, any `max` | Vector unchanged (single entry, always kept). |
| `max = Some(0)` | Only first entry kept (budget = 0 but minimum 1 is enforced). |
| `max = None` | No truncation. |
| `max = Some(u64::MAX)` | No truncation (`NO_LIMIT`). |
| All entries fit within budget | No truncation. |
| First entry alone exceeds budget | Only first entry kept (minimum override). |

---

## Examples

From the doctest in `src/util.rs` (entries each serialise to ~100 bytes):

```
entries = [e₁, e₂, e₃, e₄, e₅]   (5 entries, each ~100 bytes)
limit_size(&mut entries, Some(220))
→ entries = [e₁, e₂]             (220 bytes fits 2 entries; 3rd would exceed)

limit_size(&mut entries, Some(0))
→ entries = [e₁]                 (budget 0, but minimum 1 preserved)
```

---

## Implementation Notes

The current implementation accumulates sizes in a `u64`. On 32-bit systems, `compute_size()` returns a `u32` cast to `u64`. Potential overflow of the accumulated `size` variable when entries are very large is **not** defended against. The spec does not account for this overflow; the model assumes non-overflowing inputs.

The scan is performed with `take_while` — the first entry is always counted but the predicate is structured so the first entry always satisfies it (the `if size == 0` branch unconditionally returns `true` for the first element).

---

## Inferred Intent

The function is used throughout the Raft implementation to cap the size of `AppendEntries` RPC messages. The "always keep at least one entry" rule is a protocol-level decision: a zero-entry batch would be meaningless and could stall replication. This constraint is deliberately hard-coded in the function.

---

## Open Questions

1. **Overflow behaviour**: What should happen if cumulative `size` overflows `u64`? Is this considered impossible in practice? The spec should clarify whether overflow is a precondition violation or silently handled.

2. **Generic `T`**: The function is generic over `T: PbMessage + Clone`. The spec abstracts this to a size function `size : α → ℕ`. Is the monotonicity/non-negativity of `compute_size` an invariant we should encode?

3. **Maximality vs. prefix-of-prefix**: The current greedy scan finds the longest fitting prefix. Is there a use case where a non-contiguous subset (e.g., small scattered entries) would be preferable? (Probably not, given Raft semantics require contiguous log entries — but worth confirming.)

---

## Lean Modelling Plan (Task 3)

Abstract away protobuf-specifics. Model as:

```lean
-- Abstract size function
variable (size : α → ℕ)

-- The pure functional model
def limitSize (entries : List α) (max : Option ℕ) : List α := ...
```

Key propositions to state:
1. `limitSize_prefix : limitSize entries max = entries.take k` for some `k`
2. `limitSize_nonempty : entries ≠ [] → limitSize entries max ≠ []`
3. `limitSize_noop_none : limitSize entries none = entries`
4. `limitSize_noop_unlimited : limitSize entries (some ∞) = entries`
5. `limitSize_size_bound : ...`
6. `limitSize_maximality : ...`
