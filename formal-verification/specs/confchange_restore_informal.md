# `to_conf_change_single` and `restore` — Informal Specification

**Source**: `src/confchange/restore.rs`

🔬 *Lean Squad — auto-generated informal specification.*

---

## Overview

`to_conf_change_single(cs: &ConfState) -> (Vec<ConfChangeSingle>, Vec<ConfChangeSingle>)`
translates a Raft `ConfState` (a snapshot of cluster membership) into two lists of
primitive configuration change operations: `(outgoing, incoming)`.

`restore(tracker, next_idx, cs)` uses these two lists, together with `Changer`, to
rebuild the ConfState from scratch on an empty tracker.

---

## `to_conf_change_single`

### Purpose

The function solves the *reconstruction problem*: given a `ConfState` — which may
describe a joint configuration — produce a pair `(outgoing, incoming)` such that:

1. Start from an **empty** configuration.
2. Apply each change in `outgoing` via `Changer::simple` → produces the
   "outgoing voters" configuration (the left side of the joint config).
3. Apply `incoming` via `Changer::enter_joint` (or, if `outgoing` is empty, via
   repeated `Changer::simple`) → produces a configuration that matches `cs`.

### Input / Output

**Input**: A `ConfState` with fields:
- `voters`: the new (incoming) voter set  
- `voters_outgoing`: the old (outgoing) voter set (non-empty iff in joint state)
- `learners`: current learners
- `learners_next`: learners staged in joint state (will become learners when leaving joint)
- `auto_leave`: flag for automatic joint-state exit

**Output**: `(outgoing, incoming)` where both are `Vec<ConfChangeSingle>`.

### Construction Rules (Postconditions)

Let `V_new = cs.voters`, `V_old = cs.voters_outgoing`,
`L = cs.learners`, `L_next = cs.learners_next`.

1. **`outgoing`**: one `AddNode` for each id in `V_old`, in order:  
   `outgoing = [AddNode(id) | id ← V_old]`

2. **`incoming`**: a concatenation of four segments, in order:
   - Remove each outgoing voter: `[RemoveNode(id) | id ← V_old]`
   - Add each incoming voter:    `[AddNode(id)   | id ← V_new]`
   - Add each learner:           `[AddLearner(id)| id ← L]`
   - Add each staged learner:    `[AddLearner(id)| id ← L_next]`

3. **Non-joint shortcut**: `outgoing = [] ↔ V_old = []`

4. **Length properties**:
   - `|outgoing| = |V_old|`
   - `|incoming| = |V_old| + |V_new| + |L| + |L_next|`

5. **Change types**: every element of `outgoing` is `AddNode`; `incoming` consists of
   `|V_old|` `RemoveNode` ops, followed by `|V_new|` `AddNode` ops, followed by
   `|L| + |L_next|` `AddLearner` ops.

6. **IDs in outgoing**: exactly `V_old` (each appears once in order).

7. **IDs in incoming** (by segment):
   - Segment 0 (RemoveNode): exactly `V_old`
   - Segment 1 (AddNode):    exactly `V_new`
   - Segment 2 (AddLearner): exactly `L ++ L_next`

### Preconditions

- The `ConfState` is well-formed (standard Raft invariants hold on the input,
  but the function itself does not validate this).

### Edge Cases

- **Empty `V_old`**: `outgoing = []`, `incoming` has no `RemoveNode` ops.
  The overall `restore` path uses `simple` repeatedly (no joint state).
- **Empty `V_new`**: `incoming` has no `AddNode` ops (may produce an empty
  incoming config — the `Changer::enter_joint` call would fail; but this is
  expected to be prevented by the caller passing a well-formed `ConfState`).
- **Empty `L` and `L_next`**: `incoming` has only remove + add voter ops.

### Inferred Intent

The function is a pure list-construction utility with no side effects. It does not
validate or fail — it always returns two lists. The correctness condition is that
`restore` (which calls it) produces the right config.

---

## `restore`

### Purpose

Rebuild cluster membership (in `tracker`) from a `ConfState` snapshot, starting
from an empty tracker. Used during log replay or snapshot application.

### Algorithm

1. Call `to_conf_change_single(cs)` to get `(outgoing, incoming)`.
2. If `outgoing` is empty: apply each op in `incoming` via `Changer::simple`.
3. Otherwise:
   a. Apply each op in `outgoing` via `Changer::simple` (one at a time).
   b. Apply `incoming` in one shot via `Changer::enter_joint(cs.auto_leave, incoming)`.

### Postcondition

After `restore`, `tracker` represents the configuration described by `cs`:
- Voter set (incoming) = `cs.voters`
- Voter set (outgoing) = `cs.voters_outgoing` (if joint) or `∅`
- Learners = `cs.learners`
- LearnersNext = `cs.learners_next`

### Preconditions

- `tracker` must represent an empty configuration at call time.
- `cs` must be a valid `ConfState` (Raft invariants: voters disjoint from
  learners, etc.).

### Open Questions

1. Is `restore` idempotent if called twice on the same `ConfState`?
2. What happens if `cs.voters` is empty but `cs.voters_outgoing` is non-empty
   (an anomalous ConfState)?
3. Does `restore` guarantee `tracker` is valid after the call, or can it
   partially fail and leave `tracker` in an inconsistent state?
