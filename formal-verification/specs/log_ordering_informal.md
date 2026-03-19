# Informal Specification: Log Ordering — `is_up_to_date` and `find_conflict_by_term`

> 🔬 *Lean Squad — auto-generated informal specification.*

**Source**: `src/raft_log.rs`, lines 222–251, 437–441.

---

## Purpose

Two functions govern how Raft nodes compare logs and reconcile conflicts:

1. **`is_up_to_date(last_index, term)`** — determines whether a candidate's log is *at least
   as up-to-date* as the local log, using the Raft election restriction. A candidate may
   receive a vote only if its log is at least as up-to-date as the voter's.

2. **`find_conflict_by_term(index, term)`** — given a conflicting leader log entry `(index, term)`,
   scans backward from `index` to find the largest log index `j ≤ index` such that
   `log[j].term ≤ term`. Returns `(j, Some(log[j].term))`. This gives a follower the
   best guess for where its log first diverges from the leader's.

---

## `is_up_to_date`

### Preconditions
- `last_index` is the candidate's last log index (a `u64`, modelled as `Nat`).
- `term` is the candidate's last log term.
- `self.last_index()` and `self.last_term()` are the voter's corresponding values.

### Semantics
```
is_up_to_date(last_index, term) =
    term > self.last_term()
    || (term == self.last_term() && last_index >= self.last_index())
```

### Postconditions / Invariants

- **Reflexive**: `is_up_to_date(self.last_index(), self.last_term())` is always `true`.
- **Total**: for any two logs `(i, t)` and `(j, s)`, either `is_up_to_date(i, t)` or `is_up_to_date(j, s)` holds (at least one is as up-to-date as the other, when evaluated from the other's perspective).
- **Transitive**: if `(j, s)` is up-to-date relative to `(i, t)`, and `(k, r)` is up-to-date relative to `(j, s)`, then `(k, r)` is up-to-date relative to `(i, t)`.
- **Antisymmetric**: if `(i, t)` is up-to-date relative to `(j, s)` AND `(j, s)` is up-to-date relative to `(i, t)`, then `i = j` and `t = s`.
- **Equivalent to lex-ge on (term, index)**: `is_up_to_date(i, t) ↔ (t, i) ≥ (selfTerm, selfIdx)` in lexicographic order.

### Edge Cases
- Equal logs: `is_up_to_date(self.last_index(), self.last_term()) = true` (reflexivity).
- Higher term dominates regardless of index.
- Index tiebreak: higher index wins within the same term.

---

## `find_conflict_by_term`

### Preconditions
- `index ≤ self.last_index()` (caller must ensure this; violating it returns `(index, None)` with a warning — an error path, not a useful result).
- The log has a valid entry at `index` (i.e., `term(index)` is `Ok`).
- Raft invariant: there exists at least one entry with term ≤ `term` (specifically, the dummy entry at index 0 has term 0 ≤ any term). This prevents infinite looping.

### Semantics
Scans backward from `index`, decrementing until it finds `conflict_index` with
`log[conflict_index].term ≤ term`.  Returns `(conflict_index, Some(log[conflict_index].term))`.
Returns `(conflict_index, None)` if `term(conflict_index)` errors (compacted entry).

### Postconditions / Invariants

- **Backward-bounded**: `result ≤ index` always.
- **Term condition**: when result is `(j, Some(t))`, then `t ≤ term` and `log[j].term = t`.
- **Maximality** (key): for all `k` with `j < k ≤ index`, either `log[k].term > term` or
  `term(k)` errors (i.e., `j` is the largest index satisfying the term condition).
- **Monotone in index**: if `index1 ≤ index2`, then `find_conflict_by_term(index2, term).0 ≥ find_conflict_by_term(index1, term).0` (scanning further left gives a result at least as far right).

### Edge Cases
- If `index > last_index`: returns `(index, None)` immediately (input validation).
- If `log[index].term ≤ term`: returns `(index, Some(log[index].term))` immediately (no scan needed).
- If all entries from 0 to `index` have term > `term`: would decrement past 0, which would be UB on `u64`. In practice prevented by the invariant that the dummy entry at index 0 has term 0.
  - **⚠️ Open question**: Is the dummy entry invariant enforced anywhere? The function does not explicitly check `conflict_index == 0`. If violated, `conflict_index -= 1` on `u64` wraps to `u64::MAX` — a potential panic or logic error.

### Inferred Intent
The function accelerates AppendEntries rejection by jumping backward to the latest entry
whose term is compatible with the leader, enabling `O(terms)` recovery instead of `O(entries)`.

---

## Open Questions

1. **Dummy-entry invariant**: Is there a guarantee that `term(0) = 0` always holds? If yes,
   `find_conflict_by_term` is safe for any input. If not, the `u64` underflow is a latent bug.
2. **`find_conflict` vs `find_conflict_by_term`**: `find_conflict` scans *forward* (for batch
   appends); `find_conflict_by_term` scans *backward* (for single-entry conflicts). Their
   interaction in `maybe_append` should be formalised together.
3. **Interaction with snapshots**: What if the scan reaches a compacted region (entries below
   `self.first_index()`)? The `term()` function returns `Err` in that case, and the loop stops.
   Is this always the right behaviour?
