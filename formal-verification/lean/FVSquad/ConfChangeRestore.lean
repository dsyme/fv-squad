/-!
# ConfChange Restore — Lean 4 Specification

Formal specification of `to_conf_change_single` and `restore` from
`src/confchange/restore.rs`.

## Model scope and approximations

* **Node IDs**: `Nat` (Rust uses `u64`; overflow is not modelled).
* **ConfState**: modelled as a structure carrying four `List NodeId` fields
  (voters, votersOutgoing, learners, learnersNext) and an `autoLeave : Bool`.
  We use `List` rather than `Finset` to preserve the ordering visible in the
  concrete Rust iteration (required to state length and segment-position theorems).
* **`ConfChangeSingle`**: modelled as `Change` (reusing the type from ConfChanger).
* **`restore`**: modelled as a pure function returning the final `Cfg × Prs`
  (it ignores `next_idx` and error propagation in this model; errors map to `none`).
* **`Changer::simple` / `Changer::enter_joint`**: reuse `changerSimple` and
  `enterJoint` from `ConfChanger`.
* **Omitted**: actual `ProgressTracker` internals, `apply_conf`, RPC, I/O.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- Reuse types from ConfChanger
open FVSquad.ConfChanger

namespace FVSquad.ConfChangeRestore

/-! ## ConfState model -/

/-- A Raft configuration state (snapshot of cluster membership). -/
structure ConfState where
  voters         : List NodeId
  votersOutgoing : List NodeId
  learners       : List NodeId
  learnersNext   : List NodeId
  autoLeave      : Bool
  deriving Repr

-- ---------------------------------------------------------------------------
-- `to_conf_change_single` model
-- ---------------------------------------------------------------------------

/-- Model of `to_conf_change_single`.

    Returns `(outgoing, incoming)` where:
    * `outgoing`  = AddNode for each id in votersOutgoing
    * `incoming`  = RemoveNode(V_old) ++ AddNode(V_new) ++ AddLearner(L) ++ AddLearner(L_next)
-/
def toConfChangeSingle (cs : ConfState) : List Change × List Change :=
  let outgoing := cs.votersOutgoing.map (fun id => ⟨id, ChangeType.AddNode⟩)
  let incoming :=
    cs.votersOutgoing.map (fun id => ⟨id, ChangeType.RemoveNode⟩) ++
    cs.voters.map        (fun id => ⟨id, ChangeType.AddNode⟩)     ++
    cs.learners.map      (fun id => ⟨id, ChangeType.AddLearner⟩)  ++
    cs.learnersNext.map  (fun id => ⟨id, ChangeType.AddLearner⟩)
  (outgoing, incoming)

-- ---------------------------------------------------------------------------
-- `restore` model (pure, ignoring `next_idx`)
-- ---------------------------------------------------------------------------

/-- Apply one change via `changerSimple` from the current `(cfg, prs)`.
    Returns `none` if the change is rejected. -/
def applySimple (cfg : Cfg) (prs : Prs) (c : Change) : Option (Cfg × Prs) :=
  changerSimple cfg prs [c]

/-- Apply a list of changes one at a time via `changerSimple`.
    Returns `none` on the first rejection. -/
def applySimpleAll (cfg : Cfg) (prs : Prs) : List Change → Option (Cfg × Prs)
  | []      => some (cfg, prs)
  | c :: cs => do
    let (cfg', prs') ← applySimple cfg prs c
    applySimpleAll cfg' prs' cs

/-- Model of `restore`.  Returns the final `(cfg, prs)` or `none` on failure. -/
def restore (cfg : Cfg) (prs : Prs) (cs : ConfState) : Option (Cfg × Prs) :=
  let (outgoing, incoming) := toConfChangeSingle cs
  if outgoing.isEmpty then
    applySimpleAll cfg prs incoming
  else do
    let (cfg1, prs1) ← applySimpleAll cfg prs outgoing
    enterJoint cfg1 prs1 cs.autoLeave incoming

-- ---------------------------------------------------------------------------
-- Propositions about `toConfChangeSingle`
-- ---------------------------------------------------------------------------

-- ~~~ Structure of outgoing ~~~

/-- PROP-1  outgoing is always a list of AddNode changes. -/
theorem toConfChangeSingle_outgoing_addNode (cs : ConfState) :
    ∀ c ∈ (toConfChangeSingle cs).1, c.changeType = ChangeType.AddNode := by
  intro c hmem
  simp only [toConfChangeSingle] at hmem
  simp only [List.mem_map] at hmem
  obtain ⟨id, _, rfl⟩ := hmem
  rfl

/-- PROP-2  Length of outgoing equals length of votersOutgoing. -/
theorem toConfChangeSingle_outgoing_length (cs : ConfState) :
    (toConfChangeSingle cs).1.length = cs.votersOutgoing.length := by
  simp [toConfChangeSingle]

/-- PROP-3  The node IDs in outgoing are exactly votersOutgoing. -/
theorem toConfChangeSingle_outgoing_ids (cs : ConfState) :
    (toConfChangeSingle cs).1.map (·.nodeId) = cs.votersOutgoing := by
  simp [toConfChangeSingle, Function.comp]

-- ~~~ Structure of incoming ~~~

/-- PROP-4  Length of incoming = |V_old| + |V_new| + |L| + |L_next|. -/
theorem toConfChangeSingle_incoming_length (cs : ConfState) :
    (toConfChangeSingle cs).2.length =
    cs.votersOutgoing.length + cs.voters.length +
    cs.learners.length + cs.learnersNext.length := by
  simp [toConfChangeSingle, List.length_append, List.length_map]
  omega

/-- PROP-5  Non-joint shortcut: outgoing = [] ↔ votersOutgoing = []. -/
theorem toConfChangeSingle_outgoing_empty_iff (cs : ConfState) :
    (toConfChangeSingle cs).1 = [] ↔ cs.votersOutgoing = [] := by
  simp [toConfChangeSingle, List.map_eq_nil]

/-- PROP-6  When votersOutgoing = [], incoming has no RemoveNode ops in the
    first segment (the whole RemoveNode prefix is empty). -/
theorem toConfChangeSingle_no_remove_when_non_joint (cs : ConfState)
    (h : cs.votersOutgoing = []) :
    ∀ c ∈ (toConfChangeSingle cs).2,
      c.changeType ≠ ChangeType.RemoveNode := by
  simp only [toConfChangeSingle, h, List.map_nil, List.nil_append,
             List.mem_append, List.mem_map]
  rintro c (⟨id, _, rfl⟩ | ⟨id, _, rfl⟩ | ⟨id, _, rfl⟩)
  · simp
  · simp
  · simp

/-- PROP-7  The first |V_old| elements of incoming are RemoveNode changes. -/
theorem toConfChangeSingle_incoming_prefix_removeNode (cs : ConfState) (i : Nat)
    (hi : i < cs.votersOutgoing.length) :
    ((toConfChangeSingle cs).2.get ⟨i, by simp [toConfChangeSingle]; omega⟩).changeType
      = ChangeType.RemoveNode := by
  simp only [toConfChangeSingle]
  simp only [List.get_append_left (by simp [List.length_map]; exact hi)]
  simp [List.get_map]

/-- PROP-8  The node IDs in the RemoveNode prefix are exactly votersOutgoing. -/
theorem toConfChangeSingle_incoming_remove_ids (cs : ConfState) :
    (((toConfChangeSingle cs).2.take cs.votersOutgoing.length).map (·.nodeId))
      = cs.votersOutgoing := by
  simp [toConfChangeSingle, List.take_append_of_le_length]

-- ~~~ Interaction with applyAll ~~~

/-- PROP-9  `applySimpleAll` on an empty change list is the identity. -/
theorem applySimpleAll_nil (cfg : Cfg) (prs : Prs) :
    applySimpleAll cfg prs [] = some (cfg, prs) := by
  simp [applySimpleAll]

/-- PROP-10  `applySimpleAll` on a single change is the same as `changerSimple`. -/
theorem applySimpleAll_single (cfg : Cfg) (prs : Prs) (c : Change) :
    applySimpleAll cfg prs [c] = changerSimple cfg prs [c] := by
  simp [applySimpleAll, applySimple]

/-- PROP-11  When votersOutgoing = [], `restore` does not enter a joint state. -/
theorem restore_non_joint_path (cfg : Cfg) (prs : Prs) (cs : ConfState)
    (h_nj : cs.votersOutgoing = []) :
    restore cfg prs cs =
    applySimpleAll cfg prs (toConfChangeSingle cs).2 := by
  simp [restore, toConfChangeSingle, h_nj]

/-- PROP-12  When votersOutgoing ≠ [], `restore` enters a joint state. -/
theorem restore_joint_path (cfg : Cfg) (prs : Prs) (cs : ConfState)
    (h_j : cs.votersOutgoing ≠ []) :
    ∃ cfg1 prs1,
      applySimpleAll cfg prs (toConfChangeSingle cs).1 = some (cfg1, prs1) ∧
      restore cfg prs cs = enterJoint cfg1 prs1 cs.autoLeave (toConfChangeSingle cs).2 := by
  simp only [restore]
  rw [show (toConfChangeSingle cs).1.isEmpty = false from by
        simp [List.isEmpty_iff, (toConfChangeSingle_outgoing_empty_iff cs).not.mpr h_j]]
  simp only [ite_false]
  rcases h_apply : applySimpleAll cfg prs (toConfChangeSingle cs).1 with
  | none => exact ⟨_, _, by simp [h_apply], by simp [restore, h_apply]⟩
  | some ⟨cfg1, prs1⟩ =>
    exact ⟨cfg1, prs1, rfl, by simp [restore, h_apply]⟩

-- ~~~ Round-trip example ~~~

/-- Example: non-joint ConfState is reconstructed without joint state. -/
example :
    let cs : ConfState := ⟨[1, 2, 3], [], [5], [], false⟩
    let cfg₀ : Cfg := ⟨∅, ∅, ∅, ∅, false⟩
    let prs₀ : Prs := ∅
    (toConfChangeSingle cs).1 = [] ∧
    (toConfChangeSingle cs).2.length = 4 := by
  native_decide

/-- Example: joint ConfState produces non-empty outgoing. -/
example :
    let cs : ConfState := ⟨[1, 2, 3], [1, 2, 4, 6], [5], [4], false⟩
    (toConfChangeSingle cs).1.length = 4 ∧
    (toConfChangeSingle cs).2.length = 8 := by
  native_decide

end FVSquad.ConfChangeRestore
