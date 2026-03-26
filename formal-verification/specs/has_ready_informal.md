# Informal Specification: `RawNode::has_ready`

> 🔬 *Lean Squad — informal specification.*  
> **Source**: `src/raw_node.rs`  
> **Current phase**: 2 (Informal Spec)

---

## Purpose

`RawNode::has_ready` is a pure Boolean predicate that tells the application whether
there is outstanding work to process. The application should call it before
calling `ready()` to avoid unnecessary overhead when there is nothing to do.

Returning `true` means: "at least one of the seven observable conditions holds —
call `ready()` to collect the work." Returning `false` means: "there is currently
nothing for the application to do — skip this tick."

---

## Preconditions

No mutation occurs. The predicate is read-only with respect to the `RawNode` state.

---

## Postconditions

Returns `true` if and only if at least one of the following seven conditions holds
at the time of the call:

| # | Condition | Meaning |
|---|-----------|---------|
| C1 | `!raft.msgs.is_empty()` | There are outbound messages queued to send to peers |
| C2 | `raft.soft_state() != self.prev_ss` | Leadership or node role has changed since last `ready()` |
| C3 | `raft.hard_state() != self.prev_hs` | Term, vote, or committed index changed (needs durable write) |
| C4 | `!raft.read_states.is_empty()` | Completed read-index requests are available for the application |
| C5 | `!raft.raft_log.unstable_entries().is_empty()` | New log entries are waiting to be persisted to storage |
| C6 | `self.snap().is_some_and(|s| !s.is_empty())` | A non-empty snapshot is pending installation |
| C7 | `raft.raft_log.has_next_entries_since(self.commit_since_index)` | Committed entries are available for the application to apply |

Returns `false` if and only if all seven conditions are simultaneously false.

---

## Invariants

The seven conditions are mutually independent — any subset can hold simultaneously.
The function does not update any state; calling it twice in a row returns the same
value (it is idempotent, given no intervening `step` / `tick` calls).

---

## Edge Cases

- **All false**: common steady state when the node is idle. `has_ready` returns `false`;
  the application should not call `ready()`.
- **Only C2 true (soft state changed)**: leadership transferred; application needs to
  learn the new leader but may have no entries/messages to handle.
- **Only C3 true (hard state changed)**: term advanced without any log activity;
  application must persist the new `HardState` to stable storage.
- **C1 and C7 both true**: typical case during log replication — outbound
  `MsgAppend` messages are ready plus committed entries for the state machine.
- **C6 (snapshot)**: when a snapshot is pending, C7 (next_entries_since) should
  be false (the `ready()` function asserts this); both C5 and C6 cannot hold for
  the same index range.

---

## Examples

**Idle follower** (steady state, no activity):
- `msgs = []`, `softState = prevSS`, `hardState = prevHS`, `readStates = []`,
  `unstableEntries = []`, `snap = None`, `hasNextEntries = false`
- `has_ready() = false`

**After receiving a `MsgAppend` (follower)**:
- New entries appended to unstable log → C5 true
- `HardState.commit` may have advanced → C3 true
- `has_ready() = true`

**After `tick_election` fires** (follower becomes candidate):
- `soft_state.raft_state` changed → C2 true
- `hard_state.term` and `hard_state.vote` changed → C3 true
- `msgs` contains `MsgRequestVote` messages → C1 true
- `has_ready() = true`

**After completing a read-index request**:
- `read_states` non-empty → C4 true
- `has_ready() = true`

---

## Inferred Intent

The function is designed to be the cheapest possible check: all seven conditions
can be evaluated without any allocation or I/O — they are simple pointer/length
comparisons or field equality checks. The design implies that every state change
that an application must observe must be tracked by one of the seven conditions;
if any category of work is not listed, it would be silently missed. The completeness
of the seven conditions relative to the `ready()` output is an important correctness
criterion (but not directly proved here).

---

## Open Questions

1. **Completeness**: does `has_ready = false` guarantee that calling `ready()` would
   return a "trivially empty" ready? If so, a formal proof of this would be valuable
   but requires modelling the full `ready()` function.
2. **Condition 6 vs 5**: can C5 (unstable entries) and C6 (snapshot) both be true
   simultaneously? The `ready()` implementation asserts they cannot be for the same
   index position; this could be stated as a theorem.
3. **Atomicity**: is it safe to call `has_ready` and `ready()` without an intervening
   `step` / `tick`? The implementation assumes so (it's single-threaded); the spec
   models this by treating the node state as fixed between the two calls.
