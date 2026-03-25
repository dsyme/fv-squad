# Informal Specification: `handle_append_response`

**Source**: `src/raft.rs`, lines 1649–1863 (`RaftCore::handle_append_response`)

---

## Purpose

`handle_append_response` is the **leader-side handler** for `MsgAppendResponse`
messages — the replies sent by followers after receiving `MsgAppend` replication
messages.

It has four sequential concerns:

1. **Fast-backtrack optimisation** (`find_conflict_by_term`): when a follower
   rejects an append and provides `(reject_hint, log_term)`, the leader jumps
   the retry probe point to skip over log entries whose term already excludes a
   match — at most one probe per distinct term, instead of one per entry.

2. **Progress maintenance**: always mark the peer's progress as `recent_active`,
   update its `committed_index` from the message's `commit` field.

3. **On rejection**: attempt to decrement the next-send index (`maybe_decr_to`)
   and, if successful, switch from Replicate → Probe and re-send immediately.

4. **On acceptance**:
   - Advance `matched` and `next_idx` via `maybe_update`.
   - Transition the peer's progress state:
     - Probe → Replicate (fast re-enter replication mode).
     - Snapshot → Probe (if snapshot is caught up: `matched ≥ pending_snapshot`).
     - Replicate → (unchanged) but free inflight window up to the acknowledged index.
   - Try to advance the commit index (`maybe_commit`); if commit advanced, broadcast.
   - If the peer was paused before the update, send an append to unblock it.
   - Send as many additional appends as flow control allows (`send_append_aggressively`).
   - **Leadership transfer**: if this peer is the designated transfer target and its
     `matched` has now reached `last_index`, send `MsgTimeoutNow` to complete the
     transfer.

---

## Preconditions

- The function is only called on a leader (self.state == Leader).
- The message type is `MsgAppendResponse`.
- `m.from` must be a known peer in `self.prs`; otherwise the function returns early.

---

## Postconditions

### On rejection (`m.reject == true`)

**P1 – `recent_active` set**: `pr.recent_active = true` after any return path.

**P2 – Committed index updated**: `pr.committed_index ≥ max(old_committed_index, m.commit)`.

**P3 – `maybe_decr_to` semantics**:

- If `maybe_decr_to` returns `false` (stale rejection), nothing further changes.
- If `maybe_decr_to` returns `true`:
  - `pr.next_idx` is set to `max(matched + 1, min(rejected, next_probe_index + 1))`.
  - If `pr.state == Replicate` before decrement → `pr.state == Probe` after.
  - An append is sent to the peer.

**P4 – `next_probe_index` safety**: If the reject has `m.log_term > 0`,
`next_probe_index = find_conflict_by_term(m.reject_hint, m.log_term).0 ≤ m.reject_hint`.
This means the probe point never increases beyond the hint.

### On success (`m.reject == false`)

**P5 – `maybe_update` semantics**: If `m.index ≤ old_matched`, returns false (stale) and
the function returns without state change. Otherwise `matched = m.index`, `next_idx ≥ m.index + 1`.

**P6 – State transition**:
- `Probe → Replicate`
- `Snapshot → Probe` iff `matched ≥ pending_snapshot` (snapshot caught up)
- `Replicate` → free inflight window to `m.index`; state unchanged.

**P7 – Commit monotone**: if `maybe_commit()` fires, the committed index is non-decreasing.

**P8 – Transfer completeness**: if `m.from == lead_transferee` and `pr.matched == last_index`
after `maybe_update`, `MsgTimeoutNow` is sent to `m.from`.

---

## Invariants

- The `matched` index is always ≤ `next_idx - 1` (never exceeds the sent frontier).
- `committed_index` is monotone: it only ever increases.
- `recent_active` is set to `true` on every successful message receipt from this peer.

---

## Edge Cases

1. **Unknown peer** (`m.from` not in `prs`): early return, no state change.
2. **`m.log_term == 0` on rejection**: `next_probe_index = m.reject_hint` (no fast-backtrack).
3. **Stale rejection** (rejected index < matched, or equal + no snapshot request): `maybe_decr_to` returns false, no retry.
4. **Stale acceptance** (`m.index ≤ matched`): `maybe_update` returns false, function returns.
5. **Snapshot state caught-up**: when `matched ≥ pending_snapshot` after update, transitions to Probe.
6. **Leadership transfer complete**: exactly when `matched == last_index` and `from == lead_transferee`, a `MsgTimeoutNow` is triggered.

---

## Concrete Examples

**Example 1 — Rejection with fast-backtrack**

```
Leader log:   idx 1 2 3 4 5 6 7 8 9
              term 1 3 3 3 5 5 5 5 5

Follower log: idx 1 2 3 4 5 6
              term 1 1 1 1 2 2

MsgAppResp: reject=true, index=9, reject_hint=6, log_term=2
find_conflict_by_term(6, 2): leader term at 6 is 5 > 2, decrement → 5 (5>2) → 4 (3>2) → 3 (3>2) → 2 (3>2) → 1 (1≤2) → return (1, Some(1))
next_probe_index = 1
→ next_idx set to max(matched+1, min(9, 2)) = max(1, 2) = 2
→ probe at index 1 (send entry 2 as anchor)
```

**Example 2 — Acceptance promoting Probe→Replicate**

```
pr: state=Probe, matched=4, next_idx=5
m: reject=false, index=8
maybe_update: matched=8, next_idx=9
→ state transitions Probe→Replicate
→ maybe_commit attempted
```

**Example 3 — Acceptance in Replicate, paused window**

```
pr: state=Replicate, matched=4, next_idx=5, old_paused=true (ins.full())
m: reject=false, index=8
maybe_update: matched=8, next_idx=9 → old_paused=true
ins.free_to(8): frees window entries up to index 8
old_paused=true → send_append triggered
```

---

## Inferred Intent

The function implements the **leader-side log replication response loop** of the
Raft protocol. The core invariant being maintained is: the leader's view of each
follower's progress (`matched`, `next_idx`, `state`) is a conservative
under-approximation of the actual follower state, and the leader drives toward
convergence by retrying until `matched == last_index` for a quorum.

The fast-backtrack optimisation is a proven-correct optimisation over naive
linear probing, reducing the worst-case convergence time from O(log-length × RTT)
to O(distinct-terms × RTT).

---

## Open Questions

1. Under what conditions can `m.from == lead_transferee` and `pr.matched < last_index`
   after update (i.e., transfer timeout without completion)? — Out of scope for this spec.
2. Is there a scenario where `maybe_commit()` returns `true` but no `bcast_append`
   should happen (`should_bcast_commit()` returns false)? — The two conditions are
   independently evaluable but the interaction is not verified here.
3. The `pending_request_snapshot` field is updated inside `maybe_decr_to` on snapshot
   requests but is not directly surfaced in this function's postconditions — its
   semantics relative to `pending_snapshot` could be more precisely specified.

---

🔬 *Lean Squad — auto-generated informal specification.*
