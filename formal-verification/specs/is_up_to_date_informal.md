# Informal Specification: `RaftLog::is_up_to_date`

> 🔬 *Lean Squad — automated formal verification.*

**Source**: `src/raft_log.rs`  
**Struct**: `RaftLog<T>`  
**Function**: `is_up_to_date(&self, last_index: u64, term: u64) -> bool`

---

## Purpose

Determines whether a candidate's log is **at least as up-to-date** as this node's log,
according to the Raft paper's log comparison rule (§5.4.1).

A candidate may only win a vote if at least a quorum of voters consider its log at least
as up-to-date as their own. This function implements the per-node check.

---

## Definition

```rust
pub fn is_up_to_date(&self, last_index: u64, term: u64) -> bool {
    term > self.last_term()
        || (term == self.last_term() && last_index >= self.last_index())
}
```

---

## Preconditions

- `self` is a valid `RaftLog` with a well-defined `last_term()` and `last_index()`.
- There are no preconditions on `last_index` or `term`; any `u64` values are accepted.

---

## Postconditions

Returns `true` if and only if the candidate log `(term, last_index)` is at least as
up-to-date as the voter's log `(self.last_term(), self.last_index())` under the Raft
log comparison order.

Formally:

```
is_up_to_date(last_index, term) = true
  ↔  term > last_term  ∨  (term = last_term ∧ last_index ≥ self.last_index())
```

---

## The Raft Log Ordering

The function implements a total lexicographic order on log IDs `(term, index)`:

```
(t1, i1) ≥_log (t2, i2)  ↔  t1 > t2  ∨  (t1 = t2 ∧ i1 ≥ i2)
```

This is just lexicographic order with `term` as the primary key and `index` as the
secondary key:

- **Term dominates**: A log whose last entry has a higher term is always more up-to-date,
  regardless of length. This reflects the fact that terms are monotone in Raft — a higher
  term means more recent activity.
- **Index breaks ties**: When terms are equal, the longer log (higher last index) is
  considered more up-to-date.

---

## Invariants

1. **Reflexivity**: `is_up_to_date(self.last_index(), self.last_term()) = true`.
   Every log is at least as up-to-date as itself.

2. **Totality**: For any two log IDs `(t1, i1)` and `(t2, i2)`, at least one is
   at least as up-to-date as the other (the relation is total).

3. **Transitivity**: If A ≥_log B and B ≥_log C then A ≥_log C.

4. **Antisymmetry**: If A ≥_log B and B ≥_log A, then A = B (same term and index).

5. **Higher term wins unconditionally**: If `term > self.last_term()`, the result is
   `true` regardless of `last_index`.

6. **Lower term always loses**: If `term < self.last_term()`, the result is `false`
   regardless of `last_index`.

---

## Edge Cases

| Scenario | Result | Reason |
|---|---|---|
| `term = last_term`, `last_index = last_index` | `true` | Reflexivity |
| `term = last_term`, `last_index > last_index` | `true` | Longer log wins |
| `term = last_term`, `last_index < last_index` | `false` | Shorter log loses |
| `term > last_term`, any `last_index` | `true` | Higher term always wins |
| `term < last_term`, any `last_index` | `false` | Lower term always loses |
| `term = 0`, `last_index = 0`, vs `last_term = 0`, `last_index = 0` | `true` | Zero log equal to zero log |
| Very large `last_index`, but `term < last_term` | `false` | Term dominates |

---

## Examples

Let the voter's log be `(last_term=3, last_index=10)`:

| Candidate `(term, last_index)` | Result | Reason |
|---|---|---|
| `(3, 10)` | `true` | Equal (reflexivity) |
| `(3, 11)` | `true` | Same term, longer log |
| `(3, 9)` | `false` | Same term, shorter log |
| `(4, 1)` | `true` | Higher term, index irrelevant |
| `(2, 100)` | `false` | Lower term, index irrelevant |
| `(3, 0)` | `false` | Same term, shorter log |

---

## Context in Raft

In `src/raft.rs`, `is_up_to_date` is called in the vote-handling path:

```rust
if can_vote
    && self.raft_log.is_up_to_date(m.index, m.log_term)
    && ...
{
    // grant vote
}
```

This ensures the "election restriction" from the Raft paper: a voter only grants a
vote to a candidate whose log is at least as up-to-date as the voter's. Combined with
the quorum requirement, this guarantees that any elected leader has all committed
entries.

---

## Inferred Intent

The function is a direct implementation of Raft §5.4.1. Its purpose is safety: by
ensuring that only candidates with up-to-date logs can win elections, Raft guarantees
that all committed entries are present on the eventual leader, which in turn guarantees
that committed entries are never lost.

Key safety invariant relying on this function:
> *If entry E is committed (acknowledged by a quorum), then any future leader will
> have E in its log.*

This relies on the fact that at least one quorum member has E, and that member will
only vote for candidates with logs at least as up-to-date as its own — meaning the
candidate must also have E.

---

## Open Questions

1. **Interaction with pre-votes**: `is_up_to_date` is called for both `MsgRequestVote`
   and `MsgRequestPreVote`. Are the log comparison semantics identical for both? (Likely
   yes, but worth confirming.)

2. **Relationship to `find_conflict_by_term`**: Both functions reason about log
   freshness, but from different perspectives. Could they be unified?

3. **Overflow**: With `u64`, there is no practical risk of `last_term` or `last_index`
   overflowing. The model uses `Nat` and does not model overflow.
