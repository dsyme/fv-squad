# Informal Specification: `ProgressTracker::quorum_recently_active`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

**Source**: `src/tracker.rs:336`

---

## Purpose

`quorum_recently_active(perspective_of)` determines whether a quorum of Raft cluster nodes
are considered "recently active" from the leader's perspective. It is used to implement
`CheckQuorum` — the Raft safety mechanism by which a leader steps down if it can no longer
reach a quorum of followers.

---

## Algorithm

```rust
pub fn quorum_recently_active(&mut self, perspective_of: u64) -> bool {
    let mut active = HashSet::new();
    for (id, pr) in &mut self.progress {
        if *id == perspective_of {
            pr.recent_active = true;
            active.insert(*id);
        } else if pr.recent_active {
            active.insert(*id);
            pr.recent_active = false;
        }
    }
    self.has_quorum(&active)
}
```

1. Collect the "active" set: all progress entries where `id = perspective_of` OR `recent_active = true`.
2. For the perspective node: mark as `recent_active = true` (side effect).
3. For other recently-active nodes: mark as `recent_active = false` (side effect — resets for next check).
4. Delegate to `has_quorum(&active)` to check if the active set forms a quorum.

---

## Preconditions

- `perspective_of` should be the ID of the current leader (or the node calling this function).
- In well-formed state, `perspective_of` always has an entry in `self.progress`.

---

## Postconditions

- Returns `true` iff the active set forms a majority quorum of the voter configuration.
- Side effects (not modelled in the Lean spec):
  - `self.progress[perspective_of].recent_active` is set to `true`.
  - All other nodes in the active set have their `recent_active` reset to `false`.

---

## Key Invariants

1. **Leader always active**: `perspective_of` is always in the active set (if it has a progress entry).
2. **Quorum delegation**: the quorum check is delegated entirely to `has_quorum`, which respects the voter configuration (including joint quorum during config changes).
3. **Monotonicity**: adding more `recent_active = true` entries can only increase the chance of quorum.

---

## Edge Cases

- **Single-node cluster**: if `perspective_of` is the only voter and has a progress entry, always returns `true`.
- **Empty progress**: active set is empty. Result is `true` iff voters list is also empty.
- **Perspective not in progress**: possible in abnormal states; `perspective_of` would NOT be counted as active.
- **Learner nodes**: included in progress but not in the voter list; counted in `active` set but filtered out by `has_quorum` (which only counts against voter IDs).

---

## Examples

| Voters | Active entries | Result | Explanation |
|--------|----------------|--------|-------------|
| [1,2,3] | leader=1, nodes 2+3 active | `true` | overlap={1,2,3} ≥ 2 |
| [1,2,3] | leader=1, only | `false` | overlap={1} < 2 |
| [1] | leader=1 in progress | `true` | single-node cluster |
| [1,2,3] | none (empty progress) | `false` | no active nodes |
| [] | any | `true` | no voters, vacuously true |

---

## Inferred Intent

The function serves as the `CheckQuorum` query for the leader: "can I still communicate with enough of my cluster?" The `perspective_of` parameter allows the leader to always count itself as responsive without needing to set its own `recent_active` flag externally. The flag-clearing side effect means each check is a "rising edge" trigger — nodes must have been active since the last `quorum_recently_active` call.

---

## Open Questions

1. What happens if `perspective_of` is not a voter (e.g., it's a learner)? Then it's in the active set but doesn't contribute to the quorum count — the quorum must be formed by actual voters.
2. Is it correct that learner nodes can be in the active set? The comment in the code says "it doesn't matter whether it's learner" — because `has_quorum` filters by the voter configuration anyway.
3. The side effect of resetting `recent_active = false` on other nodes means this function must not be called multiple times per round — is there any guard against accidental double-calls?
