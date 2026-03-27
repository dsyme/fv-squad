# Informal Specification: `RaftLog::find_conflict`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

## Purpose

`find_conflict` scans a sequence of proposed log entries against the existing
Raft log and returns the index of the first discrepancy. The discrepancy is
one of two kinds:

1. **Conflict**: an entry's index is within the existing log but has a
   different term (the leader is sending a replacement entry).
2. **New**: an entry's index is beyond the end of the existing log (the
   leader is extending the log with fresh entries).

The caller (`maybe_append`) uses the returned index to decide which suffix of
the proposed entries to actually append. If there is no discrepancy, the
return value is 0 and the log is already up-to-date.

**Source location**: `src/raft_log.rs`, lines 200–216.

---

## Preconditions

1. `ents` is a slice of `Entry` values.  Each `Entry` has an `index: u64`
   (its position in the log, 1-based) and a `term: u64` (the election term in
   which it was created).
2. The `index` fields of `ents` are **strictly increasing** and **contiguous**:
   for all adjacent entries `ents[i]` and `ents[i+1]`, `ents[i+1].index ==
   ents[i].index + 1`.
3. Every entry term is positive (`term >= 1`).  The Raft protocol never
   assigns term 0 to a real entry; term 0 is a sentinel for "no entry" or
   "before the log".
4. The precondition "the first entry MUST have an index equal to the argument
   `from`" is enforced by the caller (`maybe_append`).  For the purposes of
   this function alone, `ents[0].index` may be any valid index.
5. The underlying log provides `match_term(idx, term) -> bool` and
   `last_index() -> u64`.  `match_term(idx, term)` returns `true` iff
   the log's entry at `idx` has term `term`; it returns `false` for any index
   outside `[first_index(), last_index()]` (treating out-of-range as term 0).

---

## Postconditions

Let `ents` be the input slice and `log` the abstract log (a partial function
from index to term).

### P1 — Empty input returns 0

```
find_conflict([]) = 0
```

### P2 — Non-zero result is the index of some entry in `ents`

```
find_conflict(ents) ≠ 0 →
  ∃ i, ents[i].index = find_conflict(ents)
```

### P3 — All entries before the first conflict match the log

```
find_conflict(ents) = c →
  ∀ e ∈ ents, e.index < c → match_term(e.index, e.term) = true
```

### P4 — The first non-matching entry causes the return

```
find_conflict(ents) = c  ∧  c ≠ 0 →
  match_term(c, term_of_entry_at_c_in_ents) = false
```

where `term_of_entry_at_c_in_ents` is `e.term` for the unique `e ∈ ents`
with `e.index = c`.

### P5 — Zero means all entries match the log

```
find_conflict(ents) = 0 ↔ ∀ e ∈ ents, match_term(e.index, e.term) = true
```

### P6 — Result is bounded by the first entry's index

```
find_conflict(ents) ≠ 0 → find_conflict(ents) ≥ ents[0].index
```

### P7 — Result is bounded by the last entry's index

```
find_conflict(ents) ≠ 0 → find_conflict(ents) ≤ ents[last].index
```

### P8 — Returns the *first* non-matching index (uniqueness / minimality)

```
find_conflict(ents) = c  ∧  c ≠ 0 →
  ¬ ∃ c' < c,  c' ≥ ents[0].index  ∧  ¬ match_term(c', …)
```

Equivalently: there is no smaller index in `ents` that also fails `match_term`.

---

## Invariants

- The function is **read-only**: it does not modify the log or the entries.
- The function is **deterministic**: given the same log and the same `ents`, it
  always returns the same value.
- The function is **linear** in `len(ents)`: it performs one `match_term` call
  per entry and returns as soon as it finds a mismatch.

---

## Edge Cases

| Scenario | Expected result |
|---|---|
| `ents` is empty | 0 |
| All entries match the log exactly | 0 |
| All entries extend the log (indices > `last_index()`) | `ents[0].index` (every entry fails `match_term` since out-of-range → term 0 ≠ any positive term) |
| First entry conflicts, rest match | `ents[0].index` |
| Last entry conflicts, all prior match | `ents[last].index` |
| Single entry that matches | 0 |
| Single entry that does not match | `ents[0].index` |
| Entries with some in-range matching and some new | first index past `last_index()` |

---

## Concrete Examples (from test suite)

Log initialised with `[(1,1), (2,2), (3,3)]` (index, term pairs):

| `ents` | Expected result | Reason |
|---|---|---|
| `[]` | 0 | empty |
| `[(1,1),(2,2),(3,3)]` | 0 | all match |
| `[(2,2),(3,3)]` | 0 | suffix match |
| `[(3,3)]` | 0 | suffix match |
| `[(1,1),(2,2),(3,3),(4,4),(5,4)]` | 4 | first new entry |
| `[(4,4),(5,4)]` | 4 | first new entry |
| `[(1,4),(2,4)]` | 1 | first entry conflicts (term 4 ≠ 1) |
| `[(2,1),(3,4),(4,4)]` | 2 | second entry conflicts (term 1 ≠ 2) |
| `[(3,1),(4,2),(5,4),(6,4)]` | 3 | third entry conflicts (term 1 ≠ 3) |

---

## Inferred Intent

The function is the first step of Raft's **AppendEntries** processing.  When a
leader sends a batch of entries, the follower must decide where its log
diverges from the leader's.  The return value tells `maybe_append` exactly
which entry to start appending from:

- Return 0 → log is already consistent; just advance `committed`.
- Return c ≤ `last_index()` → log diverges at `c`; truncate and re-append
  from `c`.
- Return c > `last_index()` → all proposed entries are new; append from `c`.

The Raft safety property requires that once a conflicting entry is found, all
entries from that point on must be replaced (they may have been proposed by a
different leader in a different term).  The scan stopping at the *first*
mismatch is therefore essential — entries before `c` are known-consistent and
must not be re-written.

---

## Lean Model

The function will be modelled in terms of an **abstract log**, abstracting away:

- The split between `Unstable` and stable storage
- I/O errors from `Storage::term` (the model assumes a total term function)
- Logging side effects
- The `entry_type`, `data`, and `context` fields of `Entry` (irrelevant to
  this function)

The Lean model needs:
- A type `LogEntry := { index : Nat, term : Nat }`
- An abstract log modelled as a function `log : Nat → Nat` (index → term,
  with 0 for out-of-range)
- `matchTerm (log : Nat → Nat) (idx term : Nat) : Bool := log idx == term`
- `findConflict (log : Nat → Nat) (ents : List LogEntry) : Nat`

The key theorems (P1–P8 above, plus the P5 biconditional) are all
straightforwardly provable by induction on `ents`.

---

## Open Questions

1. **What constitutes a "valid" `ents` list?**  The precondition says indices
   must be contiguous and the first entry must equal `from`.  The function
   itself does not check this; it simply iterates.  Do the correctness
   properties above hold for non-contiguous index sequences?  They appear to,
   but the Lean model should capture contiguity explicitly to stay close to
   the Raft spec intent.

2. **Can `ents` contain entries with `term = 0`?**  By Raft convention, term 0
   is reserved.  `match_term(idx, 0)` can return `true` only for compacted
   indices that fall below `first_index() - 1` (where `term` returns 0).  The
   spec above assumes `term ≥ 1` for all input entries; this should be
   verified as an invariant of the caller.

3. **Behaviour when `ents` contains an entry at index 0?**  Index 0 is the
   "dummy" index used as a sentinel below the log.  Can this arise in practice?
   The precondition "first entry MUST have index equal to `from`" suggests
   `from ≥ 1`, but this is not enforced by `find_conflict` itself.
