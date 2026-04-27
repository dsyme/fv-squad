# Informal Specification: `ProgressTracker` as a Progress Set

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

**Source**: `src/tracker.rs` — `ProgressTracker` struct and `quorum_recently_active`,
`has_quorum`, `apply_conf_change`, `progress` map.

**Run**: 120 (2026-04-27). **Phase**: 1 (informal spec).

---

## Purpose

The `ProgressTracker` (sometimes called the *progress set* in the Raft literature)
is the leader's view of every peer's replication progress.  It maps peer IDs to
`Progress` records and provides three key group-level operations:

| Operation | Description |
|-----------|-------------|
| `quorum_recently_active(perspective_of)` | Check-Quorum liveness test |
| `has_quorum(set)` | Generic quorum membership check |
| `apply_conf_change` | Membership add/remove, preserving `all_wf` |

This spec focuses on the correctness properties of `quorum_recently_active` as a
*composed* operation — combining membership (`has_quorum`) with per-peer state
(`recent_active`) — building on the existing `ProgressTracker.lean` (PT1–PT26),
`HasQuorum.lean` (HQ1–HQ20), and `QuorumRecentlyActive.lean` (QRA1–QRA11).

---

## Algorithm: `quorum_recently_active`

```rust
pub fn quorum_recently_active(&mut self, perspective_of: u64) -> bool {
    let mut active = HashSet::new();
    for (id, pr) in &mut self.progress {
        if *id == perspective_of {
            pr.recent_active = true;    // self always counts as active
            active.insert(*id);
        } else if pr.recent_active {
            active.insert(*id);
            pr.recent_active = false;   // reset — side effect
        }
    }
    self.has_quorum(&active)            // delegate quorum check
}
```

**Step 1 — Collect active set**: iterate the progress map.
- The `perspective_of` node (the caller, always the leader) always counts as active
  and its flag is set to `true`.
- Any other peer with `recent_active = true` is added to `active`; its flag is then
  reset to `false` (so the *next* call starts fresh).

**Step 2 — Quorum test**: call `has_quorum(&active)`, which delegates to
`voters.vote_result(|id| active.get(&id).map(|_| true))`.

---

## Abstract Model

We model the progress set as a pair `(voters : Finset Id, progress : Id → Progress)` where
`Progress` carries a boolean field `recentActive : Bool`.

```lean
structure ProgressSet where
  voters : Finset Nat
  progress : Nat → Progress   -- defined for all ids in voters

def activeSet (ps : ProgressSet) (perspectiveOf : Nat) : Finset Nat :=
  ps.voters.filter (fun id =>
    id = perspectiveOf || (ps.progress id).recentActive)

def resetActive (ps : ProgressSet) (perspectiveOf : Nat) : ProgressSet :=
  { ps with progress := fun id =>
      if id = perspectiveOf then
        { (ps.progress id) with recentActive := true }
      else
        { (ps.progress id) with recentActive := false } }

def quorumRecentlyActive (ps : ProgressSet) (perspectiveOf : Nat) : Bool × ProgressSet :=
  let active := activeSet ps perspectiveOf
  let ps'    := resetActive ps perspectiveOf
  (hasQuorum ps.voters active, ps')
```

---

## Key Properties

### PS1 — Self inclusion
`perspectiveOf ∈ voters ps →`
`perspectiveOf ∈ activeSet ps perspectiveOf`

The calling node (leader) is always in the active set.

### PS2 — Active-set subset
`activeSet ps perspectiveOf ⊆ ps.voters`

The active set is a subset of voters (learners cannot form quorum).

### PS3 — Monotone: more active → more likely quorum
If `activeSet ps1 perspectiveOf ⊆ activeSet ps2 perspectiveOf` and
`quorumRecentlyActive ps1 perspectiveOf = (true, _)`, then
`quorumRecentlyActive ps2 perspectiveOf = (true, _)`.

Follows from monotonicity of `hasQuorum` (HQ5).

### PS4 — Reset is idempotent after reset
`(resetActive (resetActive ps p) p) = (resetActive ps p)`

After one call the flags are cleared; calling reset again has no effect.

### PS5 — Active-set after reset is singleton
`(activeSet (resetActive ps p) p) = {p}` (when `p ∈ voters ps`)

After a reset, only the `perspectiveOf` node counts as active on the next
call — a fresh quorum check must re-collect heartbeat responses.

### PS6 — Quorum implies non-empty active set
`quorumRecentlyActive ps p = (true, _) → activeSet ps p ≠ ∅`

### PS7 — Composition with `all_wf`
`all_wf ps.progress ps.voters →`
`all_wf (resetActive ps p).progress ps.voters`

The `all_wf` invariant (PT1–PT26) is preserved by `quorumRecentlyActive`
because `resetActive` only touches the `recentActive` boolean, not any
monotonicity-relevant fields (`match_, nextIdx, state`).

### PS8 — Quorum-active characterisation (biconditional)
`quorumRecentlyActive ps p = (true, _) ↔`
`hasQuorum ps.voters (activeSet ps p) = true`

This is definitional but makes the interface explicit.

---

## Relationship to Existing Lean Files

| Property | Depends on |
|----------|-----------|
| PS1–PS2  | `Progress.lean`, `HasQuorum.lean` basics |
| PS3      | HQ5 (monotone `hasQuorum`) |
| PS4–PS5  | `ProgressTracker.lean` PT1–PT26 (all\_wf frame) |
| PS6–PS8  | `QuorumRecentlyActive.lean` QRA1–QRA11 |

A new `ProgressSet.lean` file would re-export the abstract model above and
prove PS1–PS8 as theorems PS\_1 through PS\_8.  The file sits in **Layer 21**
of the proof architecture, above `ProgressTracker` (Layer 16) and
`QuorumRecentlyActive` (Layer 3).

---

## Correspondence Target

A `ProgressSetCorrespondence.lean` file would contain `#guard` tests
verifying `quorumRecentlyActive` on concrete progress maps, e.g.,:

- 3-node cluster, all active → `true`
- 3-node cluster, only leader active → `false` (joint) or `true` (single voter)
- 5-node cluster, 3/5 active → `true`
- After reset, all non-leader active flags are `false`

Estimated: 20–25 `#guard` assertions, abstraction level.

---

## Preconditions

- `perspectiveOf ∈ voters ps` (the leader has its own progress entry).
- `all_wf ps.progress ps.voters` (inherited from ProgressTracker invariant).

## Postconditions

- Result `fst` is `true` iff `|activeSet ps perspectiveOf|` forms a quorum.
- Result `snd` has the same membership as `ps`; only `recentActive` flags differ:
  `perspectiveOf`'s flag is `true`; all others are `false`.

---

*🔬 Lean Squad — Run 120 (automated formal verification for `dsyme/raft-lean-squad`).*
