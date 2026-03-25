# Informal Specification: `handle_append_entries`

**Source**: `src/raft.rs`, `RaftCore::handle_append_entries` (≈ lines 2499–2557)

**Target phase**: 2 — Informal Spec

---

## Purpose

`handle_append_entries` is the follower-side handler for `MsgAppend` messages from
the leader. It validates the incoming append request against the local log state and
either accepts the entries (mutating the log) or rejects them with a conflict hint
that allows the leader to quickly back-track to the first divergent entry.

---

## Preconditions

- The receiver is **not** a leader (followers and candidates call this).
- The message `m` has `msg_type = MsgAppend`.
- If `maybe_append` would detect a conflict at an already-committed index, this is
  a protocol invariant violation (Raft safety); the code panics via `fatal!` in that
  case. We treat such executions as outside the model scope.
- `m.log_term = some t` for some valid term `t`; specifically, `find_conflict_by_term`
  result is expected to carry a valid term (panic otherwise).

---

## Three control-flow paths

### Path 1 — Snapshot pending

**Condition**: `self.pending_request_snapshot != INVALID_INDEX`

**Effect**: Call `send_request_snapshot()`, return immediately.  
**Response**: No `MsgAppendResponse` is sent.

This handles the case where the follower has already asked for a full snapshot
install and should not accept further log appends until the snapshot completes.

### Path 2 — Stale message

**Condition**: `m.index < self.raft_log.committed`

**Effect**: Send `MsgAppendResponse` to `m.from` with:
- `index = committed`
- `commit = committed`
- `reject = false` (no error flag, just an informational "I'm already here")

This is a "fast-forward acknowledgement" — the follower is telling the leader
that its committed index is at least as high as the message's index. The leader
uses the `index` field to update its progress map.

### Path 3 — Normal path (accept or reject)

**Condition**: `pending_request_snapshot == INVALID_INDEX && m.index >= committed`

The handler tries `raft_log.maybe_append(m.index, m.log_term, m.commit, m.entries)`:

#### Path 3a — Accept (match)

`maybe_append` returns `Some((_, last_idx))`.

**Response** to `m.from`:
- `reject = false`
- `index = last_idx` (the last newly appended index, or `m.index + len(m.entries)`)
- `commit = raft_log.committed` (post-append; may advance due to `m.commit`)

The follower's log has been updated with the new entries, and its commit index
may have advanced to `min(m.commit, last_idx)`.

#### Path 3b — Reject (mismatch)

`maybe_append` returns `None` (term mismatch at `m.index`).

**Conflict hint computation**:
1. `hint_index = min(m.index, raft_log.last_index())`
2. `(hint_index, hint_term) = raft_log.find_conflict_by_term(hint_index, m.log_term)`

**Response** to `m.from`:
- `reject = true`
- `index = m.index` (echoes back the message's index for the leader)
- `reject_hint = hint_index` (the backtrack target for the leader; ≤ m.index)
- `log_term = hint_term` (the term at the conflict hint; ≤ m.log_term)
- `commit = raft_log.committed`

The conflict hint allows the leader to binary-search backwards efficiently to the
first index where the logs diverge (the "fast log backtracking" optimisation from
§5.3 of the extended Raft paper).

---

## Postconditions

1. **Response destination**: In all response-generating paths, `resp.to = m.from`.
2. **Stale ack**: `m.index < committed` → `resp.index = committed`, `resp.commit = committed`, `resp.reject = false`.
3. **Accept**: `maybe_append` succeeds → `resp.reject = false`, `resp.index = last_idx`.
4. **Reject**: `maybe_append` fails → `resp.reject = true`, `resp.reject_hint ≤ m.index`.
5. **Hint term bound**: On reject, `resp.log_term ≤ m.log_term`.
6. **Commit in response**: Path 3 always sets `resp.commit = raft_log.committed` (post-op).
7. **Snapshot guard**: `pending_request_snapshot ≠ INVALID_INDEX` → no response sent.

---

## Edge Cases

- **Empty entries (`m.entries = []`)**: `maybe_append` still succeeds as a "probe"
  (term matches at `m.index`). `last_idx = m.index`. The response is an acceptance
  confirming the follower is at that index.
- **`m.index = 0`**: The leader is probing from the beginning; `maybe_append` checks
  the dummy entry term (always 0).
- **`hint_index = 0`**: `findConflictByTerm` returns 0 when stepping back to the
  beginning. `hint_term = logTerm(0) = some 0`. Response carries `reject_hint = 0`.
- **Committed index advancing**: On accept with a large `m.commit`, the follower's
  commit advances to `min(m.commit, last_idx)`. This may allow applying new entries.

---

## Invariants Maintained

- **Commit monotonicity**: `raft_log.committed` never decreases.
- **Log safety**: Accepted entries only overwrite entries at or after the first
  conflicting position (never truncating committed entries — preconditioned away).

---

## Open Questions

1. **Stale reject flag**: Path 2 sends `reject = false` even though the message is
   stale. Is this intentional? The leader relies on the `index` value (= committed)
   to update progress, not the reject flag. Is there a case where this causes the
   leader to misidentify the response?
2. **Commit field in reject**: Is `resp.commit = raft_log.committed` in the reject
   path used by the leader for any purpose beyond logging?
3. **hint_term = None panic**: The `fatal!` call on `hint_term.is_none()` — is this
   reachable if the log is entirely compacted between `m.index` and 0? The dummy
   entry at index 0 should prevent it, but this should be stated as an invariant.

---

## Examples

| Scenario | `m.index` | `committed` | `maybe_append` | `resp.reject` | `resp.index` |
|----------|-----------|-------------|----------------|---------------|--------------|
| Stale | 3 | 5 | — | false | 5 |
| Accept, 2 entries | 5 | 5 | Some(_, 7) | false | 7 |
| Reject, no match | 5 | 5 | None | true | 5 |
| Empty probe | 5 | 5 | Some(_, 5) | false | 5 |
| Snapshot pending | any | any | — | — | (none sent) |

---

> 🔬 *Generated by Lean Squad automated formal verification.*
