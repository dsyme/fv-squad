# Informal Specification: `ProgressTracker::quorum_recently_active`

> File: `src/tracker.rs` — `quorum_recently_active(&mut self, perspective_of: u64) -> bool`

---

## Purpose

`quorum_recently_active` answers the question: *"Has a quorum of voters communicated with
this leader recently?"* It is used by the Raft leader's `check_quorum` mechanism to detect
network partitions: if the leader cannot hear from a quorum, it steps down voluntarily
(see `check_quorum_active` in `src/raft.rs`).

The function has a **side effect**: after it runs, all `recent_active` flags in the
progress tracker are reset to `false`, except for the calling node (which is set to `true`).
This means the next call to `quorum_recently_active` will only count activity observed
after this reset.

---

## Implementation Summary

```rust
pub fn quorum_recently_active(&mut self, perspective_of: u64) -> bool {
    let mut active = HashSet::new();
    for (id, pr) in &mut self.progress {
        if *id == perspective_of {
            pr.recent_active = true;   // self is always marked active
            active.insert(*id);
        } else if pr.recent_active {
            active.insert(*id);
            pr.recent_active = false;  // reset after counting
        }
    }
    self.has_quorum(&active)  // check if active set forms a quorum
}

pub fn has_quorum(&self, potential_quorum: &HashSet<u64>) -> bool {
    self.conf.voters.vote_result(|id| potential_quorum.get(&id).map(|_| true)) == VoteResult::Won
}
```

---

## Preconditions

- `perspective_of` is the caller's own node ID (always the leader's ID in practice)
- The function may be called by the leader only
- `perspective_of` is typically present in `self.progress` (though the code handles the
  case where it is not, since iterating over progress will just not encounter it)

---

## Postconditions

### Return value
- Returns `true` iff the set of recently-active peers (including self) forms a quorum
  according to `self.conf.voters.vote_result`
- Equivalently, returns `true` iff a majority of voters are in the active set

### State changes
- `perspective_of.recent_active` is set to `true`
- All other peers' `recent_active` is set to `false` (cleared)
- No other fields of `Progress` are modified
- `self.conf` (voter configuration) is unchanged

---

## Invariants

**Active set construction**:
The active set is exactly:
```
active = { id | id == perspective_of } ∪ { id | id ≠ perspective_of ∧ recent_active[id] = true }
       = { id | id == perspective_of ∨ recent_active[id] = true }
```
(where `recent_active` refers to the state *before* this call)

**Quorum check against voters only**:
The `active` set may include learners (nodes in `progress` but not in `voters`), but
`has_quorum` uses `voters.vote_result` which only considers voter IDs. So learner presence
in `active` does not affect the result. The effective active set for the quorum check is
`active ∩ voters`.

**Self-inclusion property**:
`perspective_of` is always added to `active`, regardless of its `recent_active` flag.
This ensures the leader always counts itself as active.

---

## Edge Cases

1. **Empty voter set**: `voteResult` on an empty set returns `Won` (Raft's majority function:
   `majority(0) = 1 > 0`, but per `MajorityQuorum.lean`, the `Won` threshold is 0 of 0 = trivially satisfied). The call returns `true`.

2. **Single-node cluster**: `perspective_of` is the only voter. The active set always contains
   `perspective_of`. `majority(1) = 1` and `|active ∩ voters| ≥ 1`, so returns `true` always.

3. **perspective_of not in voters**: Possible if the leader is being removed from the
   configuration during a joint config transition. In this case, `perspective_of ∈ active`
   but may not contribute to the quorum check. The quorum is decided purely by voter IDs.

4. **All peers inactive**: Only `perspective_of` is in the active set. Returns `true` iff
   `perspective_of` alone forms a quorum (single-node case) or `false` otherwise.

5. **Idempotent second call**: After this call, all `recent_active` flags except
   `perspective_of`'s are reset to `false`. A second call immediately after will have
   `active = {perspective_of} ∩ voters` and returns `true` iff `perspective_of` alone
   forms a quorum.

---

## Examples

**Example 1** — 3-node cluster, 2 active:
- Voters: `{A, B, C}`, `perspective_of = A`
- `recent_active`: A=any, B=true, C=false
- `active = {A, B}`, `|active| = 2 ≥ majority(3) = 2` → returns `true`
- After: A.recent_active = true, B.recent_active = false, C.recent_active = false

**Example 2** — 3-node cluster, only leader:
- Voters: `{A, B, C}`, `perspective_of = A`
- `recent_active`: A=any, B=false, C=false
- `active = {A}`, `|active| = 1 < majority(3) = 2` → returns `false`
- After: A.recent_active = true, B.recent_active = false, C.recent_active = false

**Example 3** — 5-node cluster, 3 active:
- Voters: `{A, B, C, D, E}`, `perspective_of = A`
- `recent_active`: A=any, B=true, C=true, D=false, E=false
- `active = {A, B, C}`, `|active| = 3 ≥ majority(5) = 3` → returns `true`

---

## Inferred Intent

The function implements the **Check Quorum** optimization from Raft (§6.2 in the Raft
dissertation): a leader periodically checks whether it can still hear from a quorum. If not,
it steps down to avoid causing issues in a partitioned network.

The design choice to include `perspective_of` unconditionally in the active set ensures
the leader always counts itself. The reset side effect ensures each check period is
independent (fresh-start semantics).

The comment in the Rust source "It doesn't matter whether it's learner" reflects the
deliberate decision to include learners in the `active` collection, but since `has_quorum`
uses the voters configuration, learners never affect the quorum result.

---

## Open Questions

1. **Joint config handling**: The actual `has_quorum` uses `JointConfig::vote_result`,
   which requires a *joint quorum* (quorum in both incoming and outgoing voter sets).
   This spec models a single `MajorityConfig`. The formal model notes this simplification.

2. **Concurrent modification**: The `progress` map is iterated mutably. Is there any
   concern about insertion/removal during the loop? (Rust's borrow checker prevents this,
   so probably not a bug, but worth noting.)

3. **perspective_of in progress**: The spec assumes `perspective_of` is in the progress
   map. If it is not (can this happen?), then `perspective_of.recent_active` is not set,
   but `active` still doesn't contain it. Clarification from maintainers would be helpful.

---

> 🔬 *Lean Squad — informal specification extracted from `src/tracker.rs`.*
