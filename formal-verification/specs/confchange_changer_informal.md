# Informal Specification: `Changer` — Joint Configuration Changes

> 🔬 *Lean Squad — automated formal verification.*  
> Source: `src/confchange/changer.rs`, `src/confchange.rs`

---

## Purpose

The `Changer` type implements Raft joint consensus configuration changes
(Section 4.3 of the Raft thesis by Ongaro). It manages transitions between
membership configurations via three operations:

- **`enter_joint`**: begin a joint configuration transition from `C_old → C_old && C_new`
- **`leave_joint`**: complete the transition from `C_old && C_new → C_new`
- **`simple`**: a single-step change that mutates the incoming config by at most one voter

The key invariant maintained throughout is the **configuration validity** checked
by `check_invariants`:
- Every voter (in both incoming and outgoing sets) has a corresponding progress entry
- Every learner has a corresponding progress entry
- Learners and voters are disjoint (no node is both a voter and a learner)
- `learners_next` nodes are always tracked as voters in the outgoing config
- When not in joint mode, `learners_next` must be empty and `auto_leave` must be false

---

## Preconditions

### `enter_joint(auto_leave, ccs)`
- The current configuration must NOT already be joint (outgoing voters must be empty)
- The current incoming voters must be non-empty (can't start joint from zero-voter config)
- `check_invariants` must hold on the current config (validated by `check_and_copy`)
- After applying `ccs`, the incoming voters must remain non-empty

### `leave_joint()`
- The current configuration MUST be joint (outgoing voters must be non-empty)
- `check_invariants` must hold on the current config

### `simple(ccs)`
- The current configuration must NOT be joint
- After applying `ccs`, the incoming voters must differ from original by at most 1

---

## Postconditions

### `enter_joint` → `Ok((cfg, changes))`
- The resulting `cfg.voters.outgoing` equals the original `cfg.voters.incoming`
  (the old incoming becomes the outgoing — this is C_{new,old} per the Raft thesis)
- `cfg.auto_leave = auto_leave`
- `check_invariants` holds on the returned `(cfg, changes_as_prs)`
- The result is joint: `cfg.voters.outgoing` is non-empty

### `leave_joint` → `Ok((cfg, changes))`
- The resulting `cfg.voters.outgoing` is empty (no longer joint)
- All nodes in `learners_next` are moved into `learners`
- Nodes that were only in `outgoing` (not in `incoming` or `learners`) are removed
- `cfg.auto_leave = false`
- `check_invariants` holds on the returned `(cfg, changes_as_prs)`

### `simple` → `Ok((cfg, changes))`
- The result is NOT joint: `cfg.voters.outgoing` is empty
- The incoming voters differ from the original by at most one element
- `check_invariants` holds on the returned `(cfg, changes_as_prs)`

---

## Invariants

### Configuration Well-formedness (`check_invariants`)
Let `INV(cfg, prs)` denote:
1. **Voter coverage**: `∀ id ∈ cfg.voters.incoming ∪ cfg.voters.outgoing, prs.contains(id)`
2. **Learner coverage**: `∀ id ∈ cfg.learners, prs.contains(id)`
3. **Learner-voter disjointness**: `cfg.learners ∩ cfg.voters.incoming = ∅` and `cfg.learners ∩ cfg.voters.outgoing = ∅`
4. **LearnersNext coverage**: `∀ id ∈ cfg.learners_next, prs.contains(id)`
5. **LearnersNext is staged**: `∀ id ∈ cfg.learners_next, id ∈ cfg.voters.outgoing`
6. **Non-joint extras are empty**: if `cfg.voters.outgoing = ∅` then `cfg.learners_next = ∅` and `cfg.auto_leave = false`

### enter_joint / leave_joint Round-trip
If `enter_joint` succeeds, then `leave_joint` will also succeed on the resulting config
(because `enter_joint` produces a joint config with non-empty outgoing, which satisfies
`leave_joint`'s precondition).

### Voter Counts
- After `enter_joint`: `|voters.outgoing| = |original voters.incoming|`
- After `leave_joint`: `|voters.outgoing| = 0`

---

## Edge Cases

1. **Empty config**: `enter_joint` returns an error if incoming voters is empty
2. **Already joint**: `enter_joint` returns an error if config is already joint
3. **Not joint**: `leave_joint` returns an error if config is not joint
4. **Remove-all-voters**: `apply` returns an error if ccs would remove all voters
5. **Zero node_id**: `ConfChangeSingle` with `node_id == 0` is ignored (no-op)
6. **Simple: too many changes**: returns error if symmetric difference > 1
7. **Learner already learner**: `make_learner` is idempotent — returns without changing if already a learner
8. **Node not yet tracked**: `make_voter` / `make_learner` call `init_progress` for new nodes

---

## Examples

### Example 1: Simple `enter_joint` + `leave_joint`
```
Initial: voters.incoming = {1, 2, 3}, voters.outgoing = {}, learners = {}, learners_next = {}

enter_joint(false, [AddNode(4), RemoveNode(3)]):
→ voters.incoming = {1, 2, 4}, voters.outgoing = {1, 2, 3}, learners = {}, learners_next = {}
→ is_joint = true

leave_joint():
→ voters.incoming = {1, 2, 4}, voters.outgoing = {}, learners = {}, learners_next = {}
→ is_joint = false
```

### Example 2: Voter → Learner transition via joint config (staged via learners_next)
```
Initial: voters.incoming = {1, 2, 3}, voters.outgoing = {1, 2, 3}  (joint state)
         learners_next = {}

enter_joint + apply [AddLearnerNode(3)]:
→ Node 3 is in outgoing voters, so it goes to learners_next (staged)
→ learners_next = {3}

leave_joint():
→ learners_next drained into learners: learners = {3}
→ Node 3 is in incoming? No. In new learners? Yes. So NOT removed from progress.
→ voters.outgoing = {}
```

### Example 3: check_invariants violations
- Node 5 in voters but not in progress → error "no progress for voter 5"
- Node 7 in learners ∩ voters.incoming → error "7 is in learners and incoming voters"
- Node 4 in learners_next but NOT in voters.outgoing → error "4 is in learners_next and outgoing voters"

---

## Inferred Intent

The design ensures **safe membership transitions** in a distributed Raft cluster:

1. Two-phase commit for membership changes: enter joint (both configs must agree), then leave joint (new config takes over).
2. During joint consensus, a node can be simultaneously a voter in the old config and a pending learner — this is handled safely via `learners_next`.
3. The invariant `check_invariants` acts as a **representation invariant** that is maintained across all mutations. It is checked at entry (via `check_and_copy`) and exit (at the end of each method).
4. Removing nodes that are in the outgoing-but-not-incoming set is deferred until `leave_joint`, ensuring the outgoing config's quorum is never damaged prematurely.

---

## Open Questions

1. **Commutativity**: Is the order of `ConfChangeSingle` operations in `ccs` significant? (E.g., can AddNode(x) + RemoveNode(x) appear in the same call?)
2. **Progress equality**: The Rust implementation avoids copying progress entries (it uses `IncrChangeMap` as a diff). The Lean model abstracts this — is there a case where a node appears in progress but with incorrect `is_learner` state?
3. **Symmetry of `simple` and joint**: Is it always safe to alternate between `simple` and joint changes?
4. **Auto-leave semantics**: When `auto_leave = true`, who calls `leave_joint`? This matters for safety proofs of the full protocol.
