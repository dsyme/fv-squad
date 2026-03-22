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

-- ===========================================================================
-- Phase 4 / 5: Implementation bridge lemmas
--
-- These lemmas connect the abstract spec above to concrete execution of
-- `changerSimple` / `applySimpleAll` on `AddNode` lists starting from
-- an empty config.  They prove the round-trip for the outgoing segment.
-- ===========================================================================

-- ---------------------------------------------------------------------------
-- Arithmetic helper: adding one element changes the symmetric difference by ≤ 1
-- ---------------------------------------------------------------------------

/-- The intersection of `(insert i s)` with `s` equals `s` (unconditionally). -/
private lemma insert_inter_self (s : Finset NodeId) (i : NodeId) :
    s.insert i ∩ s = s := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  exact ⟨And.right, fun hx => ⟨Or.inr hx, hx⟩⟩

/-- Adding one element to a Finset changes the symmetric-difference count by at most 1. -/
private lemma addNode_diff_le_one (cfg : Cfg) (i : NodeId) :
    (cfg.incoming.insert i).card + cfg.incoming.card -
    2 * (cfg.incoming.insert i ∩ cfg.incoming).card ≤ 1 := by
  rw [insert_inter_self]
  by_cases hmem : i ∈ cfg.incoming
  · rw [Finset.insert_eq_of_mem hmem]; simp
  · rw [Finset.card_insert_of_not_mem hmem]; omega

-- ---------------------------------------------------------------------------
-- Helper lemmas about applySimple on AddNode
-- ---------------------------------------------------------------------------

/-- The `incoming` field after `applySimple cfg prs (AddNode i)` is `cfg.incoming.insert i`. -/
private lemma applySimple_addNode_incoming_eq (cfg : Cfg) (prs : Prs) (i : NodeId)
    (hi : i ≠ 0) (hnj : isJoint cfg = false)
    (cfg' : Cfg) (prs' : Prs)
    (h : applySimple cfg prs ⟨i, ChangeType.AddNode⟩ = some (cfg', prs')) :
    cfg'.incoming = cfg.incoming.insert i := by
  simp only [applySimple, changerSimple, hnj, ite_false, applyAll, applyOne,
             show (⟨i, ChangeType.AddNode⟩ : Change).nodeId = i from rfl,
             hi, ite_true, Finset.insert_nonempty, ne_eq, not_false_eq_true] at h
  rw [insert_inter_self] at h
  split_ifs at h with hdiff
  · simp at h
  · simp_all [Option.some.injEq, Prod.mk.injEq]

/-- `applySimple cfg prs (AddNode i)` preserves `isJoint = false`. -/
private lemma applySimple_addNode_isJoint_preserved (cfg : Cfg) (prs : Prs) (i : NodeId)
    (hi : i ≠ 0) (hnj : isJoint cfg = false)
    (cfg' : Cfg) (prs' : Prs)
    (h : applySimple cfg prs ⟨i, ChangeType.AddNode⟩ = some (cfg', prs')) :
    isJoint cfg' = false := by
  simp only [applySimple, changerSimple, hnj, ite_false, applyAll, applyOne,
             show (⟨i, ChangeType.AddNode⟩ : Change).nodeId = i from rfl,
             hi, ite_true, Finset.insert_nonempty, ne_eq, not_false_eq_true] at h
  rw [insert_inter_self] at h
  split_ifs at h with hdiff
  · simp at h
  · -- cfg' = {cfg with incoming := ..., learners := ..., learnersNext := ...}
    -- outgoing field unchanged by AddNode → isJoint cfg' = isJoint cfg = false
    simp_all [Option.some.injEq, Prod.mk.injEq, isJoint]

-- ---------------------------------------------------------------------------
-- IMPL-1  Single AddNode always succeeds (non-joint, i ≠ 0)
-- ---------------------------------------------------------------------------

/-- IMPL-1  Applying a single `AddNode i` (i ≠ 0) via `changerSimple` always
    succeeds when the config is not joint. -/
theorem applySimple_addNode_succeeds (cfg : Cfg) (prs : Prs) (i : NodeId)
    (hi : i ≠ 0) (hnj : isJoint cfg = false) :
    (applySimple cfg prs ⟨i, ChangeType.AddNode⟩).isSome = true := by
  simp only [applySimple, changerSimple, hnj, ite_false, applyAll, applyOne,
             show (⟨i, ChangeType.AddNode⟩ : Change).nodeId = i from rfl,
             hi, ite_true, Finset.insert_nonempty, ne_eq, not_false_eq_true]
  rw [insert_inter_self]
  -- Goal: (if diff > 1 then none else some ...).isSome = true
  -- Prove diff ≤ 1, so the branch is always some
  split_ifs with hdiff
  · exact absurd (addNode_diff_le_one cfg i) (by omega)
  · rfl

-- ---------------------------------------------------------------------------
-- IMPL-2  After AddNode, i ∈ cfg'.incoming
-- ---------------------------------------------------------------------------

/-- IMPL-2  After `changerSimple` adds node `i` (i ≠ 0) to a non-joint config,
    `i` is in the resulting `incoming`. -/
theorem applySimple_addNode_mem_incoming (cfg : Cfg) (prs : Prs) (i : NodeId)
    (hi : i ≠ 0) (hnj : isJoint cfg = false)
    (cfg' : Cfg) (prs' : Prs)
    (h : applySimple cfg prs ⟨i, ChangeType.AddNode⟩ = some (cfg', prs')) :
    i ∈ cfg'.incoming := by
  rw [applySimple_addNode_incoming_eq cfg prs i hi hnj cfg' prs' h]
  exact Finset.mem_insert_self i cfg.incoming

-- ---------------------------------------------------------------------------
-- IMPL-3  applySimpleAll on AddNode list builds the union of ids
-- ---------------------------------------------------------------------------

/-- IMPL-3  `applySimpleAll` on a list of `AddNode` changes (all ids non-zero)
    starting from a non-joint config adds exactly those ids to `incoming`.

    Formally: if `applySimpleAll cfg prs (ids.map AddNode) = some (cfg', prs')`,
    then `cfg'.incoming = cfg.incoming ∪ ids.toFinset`. -/
theorem applySimpleAll_addNodes_incoming (ids : List NodeId)
    (h_nonzero : ∀ i ∈ ids, i ≠ 0)
    (cfg : Cfg) (prs : Prs) (hnj : isJoint cfg = false)
    (cfg' : Cfg) (prs' : Prs)
    (h : applySimpleAll cfg prs (ids.map (fun id => ⟨id, ChangeType.AddNode⟩)) = some (cfg', prs')) :
    cfg'.incoming = cfg.incoming ∪ ids.toFinset := by
  induction ids generalizing cfg prs with
  | nil =>
    simp only [List.map_nil, applySimpleAll] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp [List.toFinset, Finset.union_empty]
  | cons hd tl ih =>
    -- Unfold applySimpleAll for the head element
    simp only [List.map_cons, applySimpleAll] at h
    have hi_ne0 : hd ≠ 0 := h_nonzero hd (List.mem_cons_self _ _)
    -- IMPL-1 guarantees the head step succeeds
    have hsucc := applySimple_addNode_succeeds cfg prs hd hi_ne0 hnj
    obtain ⟨⟨cfg_hd, prs_hd⟩, h_step⟩ := Option.isSome_iff_exists.mp hsucc
    -- After substituting the head result, h reduces to the tail call
    simp only [h_step, Option.bind_some] at h
    have hnj_hd : isJoint cfg_hd = false :=
      applySimple_addNode_isJoint_preserved cfg prs hd hi_ne0 hnj cfg_hd prs_hd h_step
    have h_inc_hd : cfg_hd.incoming = cfg.incoming.insert hd :=
      applySimple_addNode_incoming_eq cfg prs hd hi_ne0 hnj cfg_hd prs_hd h_step
    have h_nonzero_tl : ∀ j ∈ tl, j ≠ 0 := fun j hj => h_nonzero j (List.mem_cons_of_mem _ hj)
    -- Apply induction hypothesis on the tail
    have key := ih h_nonzero_tl cfg_hd prs_hd hnj_hd cfg' prs' h
    rw [h_inc_hd] at key
    rw [key]
    -- Prove cfg.incoming.insert hd ∪ tl.toFinset = cfg.incoming ∪ (hd :: tl).toFinset
    simp only [List.toFinset_cons]
    rw [Finset.insert_union]

-- ---------------------------------------------------------------------------
-- IMPL-4  Main round-trip for the outgoing segment
-- ---------------------------------------------------------------------------

/-- IMPL-4  Starting from the empty config, applying the `outgoing` list from
    `toConfChangeSingle cs` yields `cfg1.incoming = cs.votersOutgoing.toFinset`.

    Follows immediately from IMPL-3 applied to the empty initial config. -/
theorem restore_outgoing_builds_incoming (cs : ConfState)
    (h_nonzero : ∀ i ∈ cs.votersOutgoing, i ≠ 0)
    (cfg₁ : Cfg) (prs₁ : Prs)
    (h : applySimpleAll ⟨∅, ∅, ∅, ∅, false⟩ ∅ (toConfChangeSingle cs).1 = some (cfg₁, prs₁)) :
    cfg₁.incoming = cs.votersOutgoing.toFinset := by
  have h_out : (toConfChangeSingle cs).1 =
      cs.votersOutgoing.map (fun id => ⟨id, ChangeType.AddNode⟩) := by
    simp [toConfChangeSingle]
  rw [h_out] at h
  have key := applySimpleAll_addNodes_incoming cs.votersOutgoing h_nonzero
    ⟨∅, ∅, ∅, ∅, false⟩ ∅ (by simp [isJoint]) cfg₁ prs₁ h
  simpa using key

end FVSquad.ConfChangeRestore
