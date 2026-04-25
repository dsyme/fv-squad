# Informal Specification: `RaftLog::maybe_commit`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: `src/raft_log.rs` — `RaftLog::maybe_commit` (line 530) and `RaftLog::commit_to` (line 304)

---

## Purpose

`maybe_commit(max_index, term)` advances the `committed` index of the Raft log to
`max_index`, but only if doing so is safe according to the Raft protocol.  It is called
by the leader whenever a new entry has been acknowledged by a quorum of followers.

`commit_to(to_commit)` is the unconditional inner operation: it sets `committed =
max(committed, to_commit)`.  It is called by `maybe_commit` when all guards pass.

The critical safety rule here is **Raft §5.4.2 (term safety)**: a leader must not
directly commit entries from *previous* terms.  Committing a stale entry could allow a
future leader with a longer log to overwrite it, violating the State Machine Safety
property.  The term check `self.term(max_index) == term` is the gate that enforces this.

---

## Preconditions

### `maybe_commit(max_index, term)`

- `max_index`: the index proposed for commitment.  May be any non-negative integer.
- `term`: the caller's current term (always the leader's term at call time).
- `self.committed`: the current highest committed index.
- `self.log`: a partial function from index to term; `self.term(max_index)` returns the
  term of the entry at `max_index`, or an error if the index is out of range or
  compacted.

### `commit_to(to_commit)`

- `to_commit`: the new committed index candidate.
- **Panic guard**: `to_commit ≤ self.last_index()` must hold; the function fatally panics
  otherwise.  This precondition is always enforced at the call site.

---

## Postconditions

### `maybe_commit(max_index, term)` — returns `bool`

**Advance case** (all three guards hold: `max_index > committed ∧ term(max_index) == term`):
- Returns `true`.
- `committed` is set to `max_index`.

**No-advance case** (any guard fails):
- Returns `false`.
- `committed` is unchanged.

The three guards are:
1. `max_index > self.committed` — no regression: never move committed backwards.
2. `self.term(max_index).is_ok_and(|t| t == term)` — **term safety**: only commit entries
   whose term matches the leader's current term.
3. (implicit) `max_index ≤ self.last_index()` — in-range: `commit_to` would panic otherwise;
   the term-lookup failure propagates as `false` via `is_ok_and`.

### `commit_to(to_commit)` — returns `()`

- If `committed >= to_commit`: no-op (no regression).
- If `committed < to_commit ≤ last_index`: `committed` is set to `to_commit`.
- If `to_commit > last_index`: **panic** (fatal, should not happen in correct protocol use).

---

## Invariants

| Invariant | Description |
|-----------|-------------|
| **Monotonicity** | `committed` never decreases; both functions preserve this. |
| **Term safety** | If `maybe_commit` advanced `committed` to `k`, then `term(k) = term` at call time. |
| **Idempotency** | Calling `maybe_commit(max_index, term)` twice with the same args returns `false` on the second call (since `max_index = committed` after the first). |
| **Range** | `committed ≤ last_index` is preserved (enforced via `commit_to`'s panic guard). |

---

## Edge Cases

| Case | Behaviour |
|------|-----------|
| `max_index ≤ committed` | Returns `false`, no change. |
| `max_index > last_index` | `self.term(max_index)` returns error → `is_ok_and` is `false` → no advance. |
| `term(max_index) ≠ term` | Returns `false` — this is the Raft §5.4.2 stale-term guard. |
| `max_index = committed + 1, correct term` | Normal advance: returns `true`, committed increases by 1. |
| `commit_to` with `to_commit = committed` | No-op (no-regression guard). |
| `commit_to` with `to_commit > last_index` | **Panic** — should never occur in correct protocol use. |

---

## Examples

**Example 1** — Normal advance:

```
committed = 5, last_index = 10, log[8] has term = 3 (current term)
maybe_commit(8, 3) → true, committed = 8
```

**Example 2** — Stale term guard (§5.4.2):

```
committed = 5, last_index = 10, log[8] has term = 2, current term = 3
maybe_commit(8, 3) → false, committed = 5
```
This prevents the "figure 8" scenario: a new leader cannot directly commit an entry
from a prior term.

**Example 3** — No-regression:

```
committed = 10, last_index = 15, log[8] has term = 3
maybe_commit(8, 3) → false, committed = 10
```

**Example 4** — Index out of range:

```
committed = 5, last_index = 7, log[20] does not exist
maybe_commit(20, 3) → false (term lookup fails → is_ok_and → false), committed = 5
```

---

## Inferred Intent

The `term` argument to `maybe_commit` is always the leader's **current** term.  The
term check enforces Raft's safety rule: a leader may only directly commit entries it
appended in its own term.  Entries from prior terms can only be committed *indirectly*
when a current-term entry is committed that logically follows them.

This is the safest encoding of §5.4.2: rather than tracking which entries are from the
current term in the log itself, the commit function simply refuses to advance committed
to any entry whose term does not match the supplied term.

The `commit_to` helper is intentionally simple and monotone — it is used in both
`maybe_commit` and in `handle_append_entries` (where the follower advances committed
to `min(leader.committed, last_new_entry)`).

---

## Open Questions

1. **`zero_term_on_err_compacted`**: The actual code uses
   `self.zero_term_on_err_compacted(self.term(max_index))` which returns `0` on error
   (compacted entries).  Since `term > 0` is always true for a current-term leader, this
   effectively turns a compacted-entry lookup into `false`.  Is `0` ever a valid term?
   (In Lean model we abstract `zero_term_on_err_compacted` away via infallible `logTerm`.)

2. **Interaction with `maybe_persist`**: Both `maybe_commit` and `maybe_persist` advance
   indices monotonically.  Is there a formal invariant linking them (e.g., `persisted ≤
   committed` or similar)?  The current Lean spec treats them independently.

3. **Commit advancement at followers**: `commit_to` is also called at followers (in
   `handle_append_entries`), but without the term check.  Is the term check only required
   at the leader?  Should the follower path be modelled separately?

---

## Connection to Lean Spec

The Lean formalization is `formal-verification/lean/FVSquad/MaybeCommit.lean`.

Key theorems:
- **MC3** (`maybeCommit_advances_iff`): advances ↔ `max_index > committed ∧ log[max_index] = some term`
- **MC4** (`maybeCommit_term`): **A6** — if advanced, `log[result] = some term`
- **MC9** (`maybeCommit_idempotent`): applying twice = applying once

MC4 is the formal proof of Raft §5.4.2 for this function.
