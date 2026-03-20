# Informal Specification: `RaftLog::maybe_commit`

**Source**: `src/raft_log.rs`, line 525  
**Target**: `RaftLog::maybe_commit(max_index: u64, term: u64) -> bool`

---

## Purpose

`maybe_commit` is called by the Raft leader (and by followers on receipt of an
`AppendEntries` message) to advance the local *committed* index.  It advances
`self.committed` to `max_index` iff the entry at `max_index` exists in the log
with the expected `term`.  It returns `true` when the committed index was
actually advanced, and `false` otherwise.

The "term check" is a critical safety gate: in Raft, a leader must never commit
an entry from a *previous* term solely based on replication count — it must only
commit entries from its *current* term (and earlier entries get committed
transitively).  Callers enforce this by only passing the leader's current term;
entries from prior terms appear in the log but will never match.

---

## Implementation (Rust)

```rust
pub fn maybe_commit(&mut self, max_index: u64, term: u64) -> bool {
    if max_index > self.committed && self.term(max_index).is_ok_and(|t| t == term) {
        self.commit_to(max_index);
        true
    } else {
        false
    }
}
```

where `commit_to` sets `self.committed = max_index` (guaranteed by the guard
that `max_index > self.committed`, so `commit_to`'s no-op branch is not taken).

---

## Preconditions

1. `max_index ≤ self.last_index()` — the entry must exist in the log
   (the caller guarantees this; `commit_to` panics/fatals if violated).
2. `term` is a valid term (≥ 1 in practice, but the model allows 0).
3. The log's `term()` function returns the term stored at each index.

---

## Postconditions

**When the function returns `true`:**
- `self.committed = max_index` after the call.
- `max_index > old_committed` (strictly advanced).
- `self.term(max_index) = Ok(term)` (entry exists at the committed index).

**When the function returns `false`:**
- `self.committed` is **unchanged**.
- At least one of the following holds:
  - `max_index ≤ self.committed` (not a strict advance), or
  - `self.term(max_index) ≠ Ok(term)` (entry absent or wrong term).

---

## Invariants

- **Committed never decreases**: each call either increases `committed` or leaves
  it unchanged.
- **Committed ≤ last_index**: the new `committed` is at most `last_index`
  (maintained by the caller; `commit_to` fatals if violated).
- **Term check as safety lock**: `committed` only advances to indices whose log
  term matches the provided term, preventing stale-term commitments.

---

## Edge Cases

| Scenario | Expected result |
|----------|----------------|
| `max_index = committed` | Returns `false`, `committed` unchanged |
| `max_index < committed` | Returns `false`, `committed` unchanged |
| `max_index > committed`, wrong term | Returns `false`, `committed` unchanged |
| `max_index > committed`, correct term | Returns `true`, `committed = max_index` |
| Calling twice with same args | Second call returns `false` (idempotent) |
| `max_index = 0` | Returns `false` (0 ≤ any committed ≥ 0) |

---

## Examples

- State: `committed = 5`, log has entry (index=7, term=3)
  - `maybe_commit(7, 3)` → `true`, `committed = 7`
  - `maybe_commit(7, 2)` → `false`, `committed = 5` (wrong term)
  - `maybe_commit(4, 3)` → `false`, `committed = 5` (not a strict advance)

---

## Inferred Intent

The function is a safe "gate" that only allows the committed pointer to advance
when both conditions are simultaneously met.  The term check is a deliberate
design choice encoding Raft's Rule 5.4.2: a leader commits an entry only when
it can certify the entry's term matches the current term.

---

## Open Questions

1. **Snapshot case**: can `max_index` refer to a snapshot entry (an index before
   `unstable.offset`)? The `term()` function handles this via storage, so it
   should work, but the approximation ignores snapshot mechanics.
2. **Overflow**: `u64` arithmetic is modelled as `Nat`; real code is safe since
   indices are bounded by log size.
3. **Concurrent callers**: the model is sequential; real code is single-threaded
   per Raft node, so this is accurate.

---

🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*
