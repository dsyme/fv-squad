# Informal Specification: `bcast_append` / `maybe_send_append`

**Target file**: `src/raft.rs` and `src/tracker/progress.rs`
**Functions covered**:
- `RaftCore::maybe_send_append` (the workhorse)
- `RaftCore::send_append` (thin wrapper calling `maybe_send_append` with `allow_empty = true`)
- `RaftCore::send_append_aggressively` (loop calling `maybe_send_append` until false)
- `Raft::bcast_append` (broadcasts append to all non-self peers)
- `RaftCore::prepare_send_entries` (fills a `MsgAppend` from log + progress)
- `Progress::is_paused` (determines whether a peer's channel is saturated)
- `Progress::update_state` (advances progress after a send)

---

## Purpose

`bcast_append` is called by the Raft leader to replicate log entries to all followers.
For each follower, it invokes `send_append`, which delegates to `maybe_send_append`.
`maybe_send_append` decides _whether_ and _how_ to send — entries via `MsgAppend`,
or a snapshot via `MsgSnapshot` if the follower has fallen too far behind.

The key concern is **flow control**: do not flood a follower that hasn't yet acknowledged
earlier messages.  This is managed through the `Progress` state machine (Probe,
Replicate, Snapshot) and an inflight window (`Inflights`).

---

## Preconditions

- Caller is the Raft leader (state == `StateRole::Leader`).
- `self.prs` contains a `Progress` for every peer id in the cluster.
- For each progress in Replicate mode, `next_idx > 0` (so that `next_idx - 1` is a
  valid log index for the term lookup).
- For snapshot paths: `pr.recent_active` must be true for a snapshot to be sent.

---

## Postconditions / Contracts

### `Progress::is_paused`

| State      | Paused iff…               |
|------------|---------------------------|
| Probe      | `paused == true`          |
| Replicate  | `ins.full() == true`      |
| Snapshot   | always (`true`)           |

**Key property**: `is_paused()` is the exclusive gate on whether any message is sent.
If `is_paused()` returns `true`, `maybe_send_append` returns `false` immediately and
no message is pushed onto `msgs`.

### `Progress::update_state`

After a successful send:

| State     | Effect                                                  |
|-----------|---------------------------------------------------------|
| Replicate | `next_idx = last + 1`; `last` added to inflight window |
| Probe     | `paused = true` (single-message probe mode)             |
| Snapshot  | **panic** — should never be called                      |

**Key property**: in Replicate mode, `update_state(last)` is strictly monotone:
`next_idx` strictly increases (as long as `last >= next_idx - 1`, i.e., entries are
not empty).

### `RaftCore::prepare_send_entries`

The outbound `MsgAppend` satisfies:
- `msg.msg_type = MsgAppend`
- `msg.index    = pr.next_idx - 1`           ← previous-entry index
- `msg.log_term = term(pr.next_idx - 1)`     ← term of previous entry
- `msg.entries  = ents`                      ← entries to replicate
- `msg.commit   = raft_log.committed`        ← current committed index

If entries is non-empty, `pr.update_state(last_entry.index)` is called, advancing
the progress.

### `RaftCore::maybe_send_append` return value

Returns `true` iff exactly one message (either `MsgAppend` or `MsgSnapshot`) was
appended to `msgs`.

Returns `false` in any of these cases:
1. `pr.is_paused()` — flow-control gate
2. `!allow_empty && entries.is_empty()` — no entries to send and caller said skip empty
3. Storage temporarily unavailable (`LogTemporarilyUnavailable`)
4. Snapshot path but `!pr.recent_active` — follower not recently active

### `Raft::bcast_append`

After `bcast_append()`, `send_append` has been called for every peer `p ≠ self.id`
that is in `self.prs`.

**Key property** (broadcast coverage): every non-self peer either:
- received a `MsgAppend` or `MsgSnapshot` (if not paused, entries/snapshot available), **or**
- was skipped silently (if paused or nothing to send).

---

## Invariants

1. **Probe single-flight**: once a Probe-mode progress has been sent to (and thus paused),
   no further replication messages are sent to that peer until the leader receives an
   `MsgAppendResponse` and calls `resume()`.

2. **Replicate inflight bound**: the number of unacknowledged in-flight messages for
   a Replicate-mode peer never exceeds `ins.cap` (the window size).

3. **Snapshot exclusivity**: a Snapshot-mode progress is always paused; the leader
   cannot send additional entries until the snapshot is acknowledged or rejected.

4. **next_idx monotonicity**: `update_state` only ever increases `next_idx`.

5. **commit piggyback**: every `MsgAppend` carries `raft_log.committed` as the commit
   index, allowing followers to advance their commit index even when receiving entries.

---

## Edge Cases

- **Empty entries, allow_empty = true**: `maybe_send_append` sends a heartbeat-like
  `MsgAppend` with no entries but with the current commit index (used to inform
  followers of commit advancement).
- **Empty entries, allow_empty = false**: returns `false` without sending.
- **Aggressive mode** (`send_append_aggressively`): keeps sending until the peer is
  paused or no entries remain, pipelining multiple `MsgAppend` messages.
- **Batching**: if `batch_append` is enabled and an in-flight `MsgAppend` already
  exists for the target peer, `try_batching` merges entries in. The entries must be
  contiguous (`is_continuous_ents`), otherwise batching fails and a new message is sent.
- **Snapshot fallback**: if `term(next_idx - 1)` fails (entry compacted) or entries
  cannot be retrieved, the leader falls back to sending a snapshot.

---

## Examples

### Example 1 — Normal Replicate Send
```
Progress { state: Replicate, matched: 5, next_idx: 6, ins: not full }
Log has entries [6, 7, 8]
→ Sends MsgAppend { index: 5, log_term: term(5), entries: [6,7,8], commit: 8 }
→ Progress after: next_idx = 9, entry 8 in inflight window
```

### Example 2 — Probe Already Paused
```
Progress { state: Probe, paused: true, next_idx: 6 }
→ maybe_send_append returns false, nothing sent
```

### Example 3 — Snapshot Mode (always paused)
```
Progress { state: Snapshot, pending_snapshot: 10 }
→ is_paused() = true → returns false immediately
```

### Example 4 — bcast_append with 3 peers (self=1, peers=2,3)
```
Peer 2: Replicate, not paused → sends MsgAppend
Peer 3: Probe, paused         → skipped
→ msgs contains exactly one MsgAppend (for peer 2)
```

---

## Inferred Intent

The design separates _decision_ (`is_paused`) from _preparation_ (`prepare_send_entries`)
from _dispatch_ (`send`). This composability is deliberate: the same `is_paused` gate
is reused for all message types (append, heartbeat, snapshot).

The inflight window in Replicate mode is not an ordering guarantee — it is a pure
congestion-avoidance mechanism. Even with the window, the protocol's correctness relies
on the log's append-only ordering properties.

---

## Open Questions for Maintainers

1. **Batching semantics**: does `try_batching` ever mutate `pr.next_idx` for the
   in-flight message's recipient, or only for the last merged entry?  The current code
   calls `pr.update_state(last_idx)` inside `try_batching`, suggesting it does — is
   this intentional and safe under reordering?
2. **Aggressive send termination**: `send_append_aggressively` loops until
   `maybe_send_append` returns false.  Is there a bound on the number of iterations
   guaranteed by the inflight window size?  (Likely yes: at most `ins.cap` messages
   before the window fills and `is_paused()` returns true.)
3. **Empty-append purpose**: when `allow_empty = true` and there are no entries, the
   leader sends a commit-only `MsgAppend`.  Under what circumstances is this called and
   what is the upper bound on such empty messages?
