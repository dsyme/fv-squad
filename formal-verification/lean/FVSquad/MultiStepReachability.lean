import FVSquad.ConcreteProtocolStep

/-!
# MultiStepReachability — N-Step Valid-AE Sequences Preserve RaftReachable

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file closes the **multi-step generalisation gap** noted in `RaftProtocol.lean`
(RP8 comment) and `RaftTrace.lean` (Remaining-work section):

> "The multi-step version (for a sequence of Raft transitions) follows by induction
>  on the trace length, applying RP8 at each step.  That induction is left for a
>  future run with a `RaftTrace` inductive type."

We provide that induction here, lifting the single-step `validAEStep_raftReachable`
(CPS2) to an arbitrary-length list of valid AppendEntries steps.

## Theorem Table

| ID  | Name                               | Status   | Description |
|-----|------------------------------------|----------|-------------|
| MS1 | `listStep_raftReachable`           | ✅ proved | ValidAEList from reachable start → RaftReachable end |
| MS2 | `listStep_safe`                    | ✅ proved | ValidAEList from reachable start → cluster-safe end |
| MS3 | `listStep_raftReachable_from_init` | ✅ proved | ValidAEList from initialCluster → RaftReachable |
| MS4 | `listStep_safe_from_init`          | ✅ proved | ValidAEList from initialCluster → cluster-safe |
| MS5 | `listStep_cci`                     | ✅ proved | ValidAEList end satisfies CommitCertInvariant |
| MS6 | `listStep_committed_mono`          | ✅ proved | Committed indices monotone across a ValidAEList |
| MS7 | `ae_sequence_no_rollback`          | ✅ proved | No committed entry overwritten across entire sequence |

**Sorry count**: 0.  All theorems are proved without `sorry`.

## Connection to the Full Proof

```
raftReachable_safe (RT2)              ← RaftTrace.lean
  ↑ uses raftReachable_cci (RT1)

listStep_safe (MS2)                   ← this file
  ↑ uses raftReachable_safe (RT2)
  ↑ uses listStep_raftReachable (MS1)
    ↑ uses validAEStep_raftReachable (CPS2) at each step
```

`listStep_safe` (MS2) provides the **complete N-step end-to-end safety certificate**:
any cluster reachable via a finite sequence of well-formed AppendEntries steps satisfies
Raft state-machine safety.  This closes the multi-step gap.

## Modelling Notes

- `ValidAEList` chains `ValidAEStep` transitions; each step may affect a different
  voter `v` and come from a different leader.  Heterogeneous sequences are fully supported.
- `ValidAEList.nil cs` is the empty sequence — the final state equals `cs`.
- `raftReachable_safe` (RT2) requires a nonempty voter list; MS2/MS4 carry this as
  a hypothesis on the final state.
-/

open FVSquad.RaftTrace
open FVSquad.ConcreteProtocolStep
open FVSquad.ConcreteTransitions
open FVSquad.RaftSafety
open FVSquad.LeaderCompleteness

namespace FVSquad.MultiStepReachability

/-- A **ValidAEList** is an inductively defined chain of `ValidAEStep` transitions.

    `nil cs`         — the empty sequence; the final state equals `cs`.
    `cons step tail` — prepend one `ValidAEStep` (from `cs₀` to `cs₁`) followed by
                       more steps from `cs₁` to `cs₂`. -/
inductive ValidAEList (E : Type) [DecidableEq E] : ClusterState E → ClusterState E → Prop where
  | nil  (cs : ClusterState E) : ValidAEList E cs cs
  | cons {cs₀ cs₁ cs₂ : ClusterState E} {lead v : Nat} {msg : AppendEntriesMsg E} :
      ValidAEStep E cs₀ lead v msg cs₁ →
      ValidAEList E cs₁ cs₂ →
      ValidAEList E cs₀ cs₂

/-! ## MS1: Every final state of a ValidAEList is RaftReachable -/

/-- **MS1** — If the starting state is `RaftReachable`, then the final state of any
    `ValidAEList` starting from it is also `RaftReachable`.

    **Proof**: induction on `ValidAEList`.
    - `nil`: trivial — start = finish.
    - `cons step tail`: apply CPS2 to get `cs₁` reachable, then IH for the tail. -/
theorem listStep_raftReachable [DecidableEq E] {cs cs' : ClusterState E}
    (hreach : RaftReachable cs)
    (hlist  : ValidAEList E cs cs') :
    RaftReachable cs' := by
  induction hlist with
  | nil  _          => exact hreach
  | cons hstep _ ih => exact ih (validAEStep_raftReachable E hreach hstep)

/-! ## MS2: Every final state is cluster-safe -/

/-- **MS2** — The final state of any `ValidAEList` from a `RaftReachable` start with
    non-empty voters is cluster-safe.

    **Proof**: MS1 → `RaftReachable cs'`; then RT2 (`raftReachable_safe`) concludes. -/
theorem listStep_safe [DecidableEq E] {cs cs' : ClusterState E}
    (hd : Nat) (tl : List Nat)
    (hvoters : cs'.voters = hd :: tl)
    (hreach  : RaftReachable cs)
    (hlist   : ValidAEList E cs cs') :
    isClusterSafe cs' :=
  raftReachable_safe hd tl cs' hvoters (listStep_raftReachable hreach hlist)

/-! ## MS3: ValidAEList from initialCluster → RaftReachable -/

/-- **MS3** — A `ValidAEList` from the `initialCluster` yields a `RaftReachable` state. -/
theorem listStep_raftReachable_from_init [DecidableEq E] {cs' : ClusterState E}
    (voters : List Nat)
    (hlist : ValidAEList E (initialCluster voters) cs') :
    RaftReachable cs' :=
  listStep_raftReachable (RaftReachable.init voters) hlist

/-! ## MS4: ValidAEList from initialCluster → cluster-safe -/

/-- **MS4** — Any finite sequence of well-formed AE steps from the initial (empty) cluster
    yields a cluster-safe final state.

    This is the simplest complete end-to-end safety statement. -/
theorem listStep_safe_from_init [DecidableEq E] {cs' : ClusterState E}
    (hd : Nat) (tl : List Nat)
    (hvoters : cs'.voters = hd :: tl)
    (hlist : ValidAEList E (initialCluster (hd :: tl)) cs') :
    isClusterSafe cs' :=
  listStep_safe hd tl hvoters (RaftReachable.init (hd :: tl)) hlist

/-! ## MS5: Every final state satisfies CommitCertInvariant -/

/-- **MS5** — The final state of a `ValidAEList` from a `RaftReachable` start satisfies
    `CommitCertInvariant`.  Combines MS1 with RT1 (`raftReachable_cci`). -/
theorem listStep_cci [DecidableEq E] {cs cs' : ClusterState E}
    (hreach : RaftReachable cs)
    (hlist  : ValidAEList E cs cs') :
    CommitCertInvariant cs' :=
  raftReachable_cci cs' (listStep_raftReachable hreach hlist)

/-! ## MS6: Committed indices are monotone across a ValidAEList -/

/-- **MS6** — For any voter `w`, committed indices only increase across a `ValidAEList`.

    **Proof**: induction; each step contributes `hcommitted_mono`; transitivity. -/
theorem listStep_committed_mono [DecidableEq E] {cs cs' : ClusterState E}
    (hlist : ValidAEList E cs cs') :
    ∀ (w : Nat), cs'.committed w ≥ cs.committed w := by
  induction hlist with
  | nil  _          => intro; exact Nat.le_refl _
  | cons hstep _ ih => intro w; exact Nat.le_trans (hstep.hcommitted_mono w) (ih w)

/-! ## MS7: No committed entry overwritten across the entire sequence -/

/-- **MS7** — For any voter `w` and index `k ≤ cs.committed w` in the *starting* state,
    the log entry at `k` is unchanged in the *final* state: `cs'.logs w k = cs.logs w k`.

    **Proof**: induction on `ValidAEList`.
    - `nil`: trivially equal.
    - `cons step tail`:
      1. CPS12 (`ae_step_no_rollback`) gives `cs₁.logs w k = cs₀.logs w k`.
      2. `hcommitted_mono` gives `cs₁.committed w ≥ k`, so the IH applies to the tail.
      3. IH: `cs₂.logs w k = cs₁.logs w k`.  Transitivity concludes. -/
theorem ae_sequence_no_rollback [DecidableEq E] {cs cs' : ClusterState E}
    (hlist : ValidAEList E cs cs') :
    ∀ (w k : Nat), cs.committed w ≥ k → cs'.logs w k = cs.logs w k := by
  induction hlist with
  | nil  _               => intros; rfl
  | cons hstep htail ih =>
    intro w k hle
    exact (ih w k (Nat.le_trans hle (hstep.hcommitted_mono w))).trans
          (ae_step_no_rollback E hstep w k hle)

/-! ## Evaluation examples -/

/-- Empty step-list from a reachable start is still reachable. -/
example (cs : ClusterState Nat) (h : RaftReachable cs) : RaftReachable cs :=
  listStep_raftReachable h (ValidAEList.nil (E := Nat) cs)

/-- Zero steps from the initial 3-voter cluster: still cluster-safe (vacuously). -/
example : isClusterSafe (initialCluster (E := Nat) [1, 2, 3]) :=
  listStep_safe_from_init (E := Nat) 1 [2, 3] rfl (ValidAEList.nil _)

end FVSquad.MultiStepReachability
