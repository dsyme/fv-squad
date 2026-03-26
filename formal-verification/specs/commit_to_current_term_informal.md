# Informal Specification: `commit_to_current_term` and `apply_to_current_term`

**Target**: `RaftCore::commit_to_current_term` and `RaftCore::apply_to_current_term`  
**File**: `src/raft.rs` (lines 590–601)  
**Phase**: 2 — Informal Spec

---

## Purpose

Both predicates are pure Boolean liveness gate functions. They check whether the
committed (or applied) log index was written in the **current Raft term** —
i.e., whether the leader has "touched" that position during its own tenure.

```rust
pub fn commit_to_current_term(&self) -> bool {
    self.raft_log.term(self.raft_log.committed).is_ok_and(|t| t == self.term)
}

pub fn apply_to_current_term(&self) -> bool {
    self.raft_log.term(self.raft_log.applied).is_ok_and(|t| t == self.term)
}
```

- `commit_to_current_term` returns `true` iff the log entry at `committed` was
  written in `self.term`.
- `apply_to_current_term` returns `true` iff the log entry at `applied` was
  written in `self.term`.

### Usage contexts

1. **`commit_to_current_term`** guards `MsgReadIndex` handling (line 2153):  
   A Raft leader must commit at least one entry from its own term before serving
   linearisable reads. Without this gate, a newly elected leader might return
   stale reads.

2. **`apply_to_current_term`** guards `check_group_commit_consistent` (line 573):  
   Ensures that group-commit consistency checks only run after the leader has
   applied an entry from its own term, preventing spurious results during warm-up.

---

## Preconditions

- `self.term ≥ 1` (Raft invariant: term starts at 0 but is incremented at first election).
- `self.raft_log.committed` and `self.raft_log.applied` are valid indices in the log
  (always true by the RaftLog invariants: `first_index() - 1 ≤ committed ≤ last_index()`).
- For normal operation (no pending `max_apply_unpersisted_log_limit`): `applied ≤ committed`.

---

## Postconditions (return value semantics)

### `commit_to_current_term`

Returns `true` iff:
- `self.raft_log.term(self.raft_log.committed)` returns `Ok(t)` **and** `t == self.term`.

Returns `false` if:
- The committed index is out-of-range (returns `Ok(0)` sentinel, which ≠ current term unless term = 0).
- The committed index refers to an entry from a prior term.
- The committed index is compacted/unavailable (returns `Err`, so `is_ok_and` → false).

### `apply_to_current_term`

Identical structure with `applied` substituted for `committed`.

---

## Invariants

1. **Term monotonicity**: Raft log entries are written in non-decreasing term order.
   Entry at index `i` has term `term(i)` such that `term(i) ≤ term(i+1)` whenever
   both are defined. This is a fundamental Raft log invariant.

2. **Term upper bound**: No log entry can be written with a term exceeding the
   current node term. So `term(i) ≤ self.term` for all defined entries.

3. **apply ≤ committed** (normal operation): Applied index never exceeds committed
   index (except transiently during restart with `max_apply_unpersisted_log_limit > 0`).

---

## Key derived property: `apply_to_current_term → commit_to_current_term`

Given invariants (1) term monotonicity, (2) term upper bound, and (3) `applied ≤ committed`:

If `apply_to_current_term` holds, then `term(applied) = self.term`.
By monotonicity: `term(committed) ≥ term(applied) = self.term`.
By upper bound: `term(committed) ≤ self.term`.
Therefore: `term(committed) = self.term`, so `commit_to_current_term` holds.

This is the key formal property: **`apply_to_current_term` implies `commit_to_current_term`**
(under the stated invariants).

---

## Edge cases

1. **`self.term = 0`**: Never occurs in normal operation (initial term is 0, but the
   first heartbeat increments it). The `Ok(0)` sentinel returned for out-of-range
   indices would match, giving a spurious `true`. In practice `term ≥ 1` is always
   true when these predicates matter.

2. **Freshly elected leader with no committed entries in current term**: Returns `false`.
   This is expected — a leader must append and commit a no-op entry to serve reads.

3. **Compacted log**: If `committed` falls below `first_index() - 1`, `term()` returns
   `Ok(0)`. This would give `true` only if `self.term == 0`, which is never the case.
   In practice: `committed ≥ first_index() - 1` is always maintained.

4. **Same term after leader re-election**: If the same node gets re-elected with
   the same term (not standard Raft, but possible in pre-vote mode), these predicates
   continue to work correctly.

---

## Examples

```
// Leader in term 5, committed at index 10 with term 5:
commit_to_current_term() = true      // term(10) = 5 = self.term

// Leader in term 5, committed at index 10 with term 4 (prior term entry):
commit_to_current_term() = false     // term(10) = 4 ≠ 5

// Follower in term 3, applied at index 7 with term 3:
apply_to_current_term() = true       // term(7) = 3 = self.term

// Follower in term 3, applied at index 7 with term 2:
apply_to_current_term() = false      // term(7) = 2 ≠ 3
```

---

## Inferred intent

The Raft protocol requires a leader to commit at least one entry from its own term
before it may safely serve reads (Raft thesis §6.4). These predicates implement that
check. The `apply_to_current_term` variant is a stronger condition (applied ≤ committed)
used in the group-commit path, which requires that the state machine has actually
applied an entry from the current term.

---

## Open questions

1. **`term = 0` edge case**: Should `commit_to_current_term` explicitly guard against
   `self.term == 0`? The current implementation returns `true` when both are `0`
   (out-of-range sentinel matches zero term), which seems like a latent bug.
   **Action**: flag in CRITIQUE.md; the Lean model exposes this case.

2. **`max_apply_unpersisted_log_limit > 0`**: When this limit is non-zero, `applied`
   can temporarily exceed `committed`. Does `apply_to_current_term` behave correctly
   in this case? The Rust comment says the invariant `applied ≤ committed` may
   temporarily break. The `apply_implies_commit` theorem would not hold then.
   **Action**: the Lean spec makes this assumption explicit.

3. **Thread safety**: These are pure reads; no mutex is needed if called within the
   `RawNode` lock. Lean models the single-threaded pure case.

---

🔬 *Lean Squad — automated formal verification.*
