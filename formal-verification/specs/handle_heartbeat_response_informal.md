# Informal Specification: `handle_heartbeat_response`

**Source**: `src/raft.rs` — `RaftCore::handle_heartbeat_response`  
**Related methods**: `Progress::update_committed`, `Progress::resume`,
`Inflights::free_first_one`, `ReadOnly::recv_ack`, `ReadOnly::advance`

---

## Purpose

Processes an incoming `MsgHeartbeatResponse` from a follower.  The function has
three distinct concerns, executed in sequence:

1. **Progress unblocking**: marks the follower as recently active, updates its
   known-committed index, and clears flow-control pause so a new append can be
   sent immediately.
2. **Catch-up trigger**: if the follower is behind (its `matched` index is
   below the leader's `last_index`) or has a pending snapshot request, sends a
   `MsgAppend` (or `MsgSnapshot`) to close the gap.
3. **ReadIndex quorum completion**: if the heartbeat carried a read-only request
   context and we are in `Safe` ReadOnly mode, counts the acknowledgment.  If a
   quorum of peers has now acknowledged the same context, all pending read
   requests up to that context are drained from the queue and dispatched as
   `MsgReadIndexResp` to the client.

---

## Preconditions

* `self` is the leader (called only from the leader message-dispatch loop).
* `m.from` identifies a valid peer (may be absent from the progress tracker if
  it has just been removed; in that case the function returns early with no
  effect).
* `m.commit` is a commit index reported by the follower (may be stale).
* `m.context` is either empty (plain heartbeat) or a read-request context token.

---

## Postconditions

Given that `m.from` is in the progress tracker (let `pr` be the mutable
progress entry):

1. **Committed index is monotonically advanced**:
   `pr.committed_index' = max(pr.committed_index, m.commit)`

2. **Peer is marked active**:
   `pr.recent_active' = true`

3. **Probe pause is cleared**:
   `pr.paused' = false`  (regardless of previous state)

4. **Inflight slot freed (Replicate + full only)**:
   If `pr.state = Replicate ∧ pr.ins.full()` then one inflight entry is
   released so the window is no longer full.
   Otherwise `pr.ins` is unchanged.

5. **Catch-up send (conditional)**:
   If `pr.matched < last_index ∨ pr.pending_request_snapshot ≠ INVALID_INDEX`
   then `send_append(m.from)` is called (which produces a message).

6. **ReadIndex advancement (conditional)**:
   Only when `read_only_option = Safe ∧ ¬m.context.is_empty()`:
   * `m.from` is recorded as an acknowledgment for the context.
   * If `has_quorum(acks_for_context)` then every pending read request in the
     queue up to and including the matched context is dequeued and a
     `MsgReadIndexResp` is sent for each.
   * If quorum not yet reached: no read responses are sent.

---

## Invariants

* **Monotone committed index**: `pr.committed_index` never decreases.
* **Liveness progress**: each heartbeat response either clears the Probe pause
  or frees an inflight slot, guaranteeing forward progress for every follower
  in steady state.
* **At-most-once read dispatch**: a pending ReadIndex entry is dispatched at
  most once — after it is dequeued by `ReadOnly::advance` it is removed from
  the map and queue.
* **Quorum safety**: read responses are dispatched only when a quorum of
  followers has acknowledged the associated heartbeat.

---

## Edge Cases

* **Unknown peer** (`m.from ∉ prs`): returns immediately; no state change.
* **`m.commit` stale** (≤ `pr.committed_index`): `update_committed` is a
  no-op; no harm.
* **Peer fully caught up** (`pr.matched = last_index`): no catch-up send is
  triggered.
* **Non-Safe ReadOnly mode**: the ReadIndex portion is skipped entirely.
* **Empty context**: the ReadIndex portion is skipped entirely.
* **Context not in pending map** (`recv_ack` returns `None`): quorum check is
  skipped; no read responses sent.
* **Inflight slot freed but paused is already false**: still freed correctly;
  subsequent replicate-mode sends are unblocked.

---

## Examples

| Situation | Outcome |
|-----------|---------|
| Probe-paused follower at term 5, `m.commit=3`, `last_index=10` | paused cleared, committed advances to 3, send_append triggered (matched < 10) |
| Replicate-mode follower, inflight full, fully caught up | slot freed, no send_append (matched = last_index) |
| Safe ReadOnly, context present, quorum not yet reached | ack recorded, no read response sent |
| Safe ReadOnly, context present, quorum reached | all pending reads up to context dispatched |

---

## Inferred Intent

The heartbeat round-trip is Raft's primary liveness mechanism: every leader
heartbeat timeout triggers a heartbeat broadcast; each response is an
opportunity to unblock a stuck follower and confirm alive-ness.  The ReadIndex
piggyback allows safe linearisable reads without a full log round-trip.

---

## Open Questions

1. **`update_committed` lower bound**: should `m.commit` be validated against
   `raft_log.committed`?  If the follower sends a spuriously high commit index
   this advances `pr.committed_index` beyond the leader's own committed index.
   Is this harmful?
2. **Inflight free-one vs reset**: `free_first_one` frees exactly one slot.
   Under what conditions would `free_to(pr.matched)` be more appropriate?
3. **ReadIndex quorum with configuration changes**: if a joint-config change is
   in progress, `has_quorum` checks both configs.  Is the piggybacked-heartbeat
   approach safe during joint config transitions?

---

🔬 *Lean Squad — auto-generated informal specification.*
