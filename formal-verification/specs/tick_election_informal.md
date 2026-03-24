# Informal Specification: `tick_election`

**Source**: `src/raft.rs`, `RaftCore::tick_election` (≈ lines 1103–1114)

**Target phase**: 2 — Informal Spec

---

## Purpose

`tick_election` is the time driver for followers and candidates. It is called once per
application "tick" while the node is in Follower or Candidate state. It increments the
local election timeout counter and, if the randomised timeout has been exceeded and the
node is promotable, triggers a new election by sending itself a `MsgHup` message.

---

## Relevant Rust code

```rust
pub fn tick_election(&mut self) -> bool {
    self.election_elapsed += 1;
    if !self.pass_election_timeout() || !self.promotable {
        return false;
    }
    self.election_elapsed = 0;
    let m = new_message(INVALID_ID, MessageType::MsgHup, Some(self.id));
    let _ = self.step(m);
    true
}
```

Where:
```rust
pub fn pass_election_timeout(&self) -> bool {
    self.election_elapsed >= self.randomized_election_timeout
}
```

And `randomized_election_timeout` is drawn uniformly from
`[min_election_timeout, max_election_timeout)` when `reset_randomized_election_timeout`
is called (at state transitions and after triggering an election).

---

## Preconditions

- Called only when the node is in Follower or PreCandidate or Candidate state.
- `randomized_election_timeout ∈ [min_election_timeout, max_election_timeout)`.
- `election_elapsed` is a non-negative integer, increasing by 1 each tick.
- `promotable` is `true` iff the node is a voter in the current configuration (i.e.,
  its own ID appears in the quorum config). Learner nodes are not promotable.

---

## Postconditions

1. **Always increments elapsed**: `election_elapsed` increases by exactly 1 before any
   guard check. This increment is unconditional.
2. **Returns false when below timeout**: If `election_elapsed (post-increment)
   < randomized_election_timeout`, returns `false` and no election is triggered.
3. **Returns false when non-promotable**: If the node is not a voter (`!promotable`),
   returns `false` even if the timeout has elapsed.
4. **Election fired**: If both conditions hold (timeout elapsed AND promotable):
   - `election_elapsed` is **reset to 0**.
   - A `MsgHup` message is sent to the node itself (triggering `step(MsgHup)`).
   - Returns `true`.
5. **Monotone elapsed (no fire)**: When the function returns `false`, `election_elapsed`
   is exactly `old_election_elapsed + 1`.

---

## Invariants

- **Elapsed is bounded by timeout**: After a fired election, `election_elapsed = 0`.
  This, combined with the increment pattern, means `tick_election` fires at most once
  per `randomized_election_timeout` ticks.
- **Only voters can call elections**: `promotable = false` is a hard guard; learner
  nodes can never trigger elections regardless of elapsed time.
- **Single trigger per timeout window**: Between any two consecutive `true` returns,
  at least `randomized_election_timeout` ticks have elapsed.

---

## Edge Cases

- **First tick**: `election_elapsed` starts at 0; after the first tick it is 1.
  Unless `randomized_election_timeout = 1` (minimum), no election fires.
- **Repeated calls after firing**: After `tick_election` returns `true`, `election_elapsed`
  is 0. The next `randomized_election_timeout - 1` calls return `false`.
- **Non-promotable with elapsed timeout**: The timeout may have been exceeded, but
  if `promotable = false` the function still returns `false`. `election_elapsed` keeps
  incrementing (it is not reset). This is intentional: when the node becomes promotable
  again (e.g., rejoins the config), the timeout may fire quickly.
- **`randomized_election_timeout = min_election_timeout`**: Fastest possible election;
  fires after exactly `min_election_timeout` ticks post-reset.

---

## Candidate Propositions for Lean Spec (Phase 3)

| ID | Property |
|----|----------|
| P1 | `tick_election_increments_elapsed`: `election_elapsed` is always `old + 1` before the guard |
| P2 | `tick_election_fires_iff`: returns `true` ↔ timeout passed AND promotable |
| P3 | `tick_election_resets_on_fire`: fires → `election_elapsed = 0` after the call |
| P4 | `tick_election_no_reset_on_false`: returns `false` → `election_elapsed = old + 1` |
| P5 | `tick_election_nonpromotable_false`: `!promotable` → always returns `false` |
| P6 | `tick_election_below_timeout_false`: `old + 1 < randomized_election_timeout` → returns `false` |

---

## Open Questions

1. **Elapsed not reset when non-promotable**: Is it intentional that `election_elapsed`
   is not reset when the timeout passes but the node is non-promotable? This means a
   node that becomes promotable might fire an election almost immediately (if elapsed
   already exceeds the next randomised timeout). Is this a concern?
2. **`step` return value ignored**: `let _ = self.step(m)` — any error from `step` is
   silently discarded. Can `step(MsgHup)` fail in a way that matters?
3. **`promotable` check order**: The check `!pass_election_timeout() || !self.promotable`
   short-circuits on `!pass_election_timeout()`. Is the order deliberate (optimisation,
   or is there a semantic reason `promotable` shouldn't be checked first)?

---

> 🔬 *Generated by Lean Squad automated formal verification.*
