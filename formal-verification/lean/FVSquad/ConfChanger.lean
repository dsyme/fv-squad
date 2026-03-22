/-!
# ConfChange Changer — Lean 4 Specification

Formal specification of `Changer::enter_joint`, `Changer::leave_joint`,
`Changer::simple`, and `check_invariants` from `raft-rs`
(`src/confchange/changer.rs`, `src/confchange.rs`).

## Model scope and approximations

* **Node IDs**: `Nat` (Rust uses `u64`; overflow is not relevant to these properties).
* **Progress map**: modelled as `Finset NodeId` — the set of node IDs that have a
  progress entry. The actual Progress struct (match index, state, inflight window, etc.)
  is omitted; only membership matters for `check_invariants`.
* **`IncrChangeMap`**: abstracted away — progress additions/removals are tracked by
  inserting/erasing from the `Prs` Finset.
* **`ConfChangeSingle`**: modelled as `Change` (variant + node id).
* **`apply` error path**: the "removed all voters" check is kept; Rust error returns map
  to `none` in `Option`.
* **Omitted**: actual `Progress` struct fields (`is_learner`, `match_idx`, …), RPC/network
  behaviour, `ProgressTracker` (we only model `Changer` and `check_invariants`).

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace FVSquad.ConfChanger

abbrev NodeId := Nat

/-- A Raft membership configuration (joint or non-joint). -/
structure Cfg where
  incoming    : Finset NodeId   -- new (or sole) voter set
  outgoing    : Finset NodeId   -- old voter set; ∅ when not in joint state
  learners    : Finset NodeId
  learnersNext : Finset NodeId  -- staged learners waiting for LeaveJoint
  autoLeave   : Bool
deriving Repr, DecidableEq

/-- Progress map: set of node IDs that have a Progress entry. -/
abbrev Prs := Finset NodeId

/-- A configuration change operation. -/
inductive ChangeType | AddNode | AddLearner | RemoveNode
  deriving Repr, DecidableEq

structure Change where
  nodeId     : NodeId
  changeType : ChangeType
  deriving Repr

-- ---------------------------------------------------------------------------
-- Core predicates
-- ---------------------------------------------------------------------------

/-- True iff the configuration is in joint state. -/
def isJoint (cfg : Cfg) : Bool := cfg.outgoing != ∅

/-- The configuration well-formedness invariant, matching `check_invariants` in Rust.
    INV(cfg, prs) holds iff:
    1. Every incoming voter has a progress entry.
    2. Every outgoing voter has a progress entry.
    3. Every learner has a progress entry.
    4. Learners and incoming voters are disjoint.
    5. Learners and outgoing voters are disjoint.
    6. Every learnersNext node has a progress entry.
    7. Every learnersNext node is an outgoing voter (it was staged there).
    8. When not joint: learnersNext = ∅ and autoLeave = false. -/
def Inv (cfg : Cfg) (prs : Prs) : Prop :=
  (∀ id ∈ cfg.incoming,    id ∈ prs)  ∧
  (∀ id ∈ cfg.outgoing,    id ∈ prs)  ∧
  (∀ id ∈ cfg.learners,    id ∈ prs)  ∧
  (∀ id, id ∈ cfg.learners → id ∉ cfg.incoming)  ∧
  (∀ id, id ∈ cfg.learners → id ∉ cfg.outgoing)  ∧
  (∀ id ∈ cfg.learnersNext, id ∈ prs) ∧
  (∀ id ∈ cfg.learnersNext, id ∈ cfg.outgoing) ∧
  (isJoint cfg = false → cfg.learnersNext = ∅ ∧ cfg.autoLeave = false)

-- ---------------------------------------------------------------------------
-- Implementation model
-- ---------------------------------------------------------------------------

/-- Apply one change.  Returns `none` only if the node_id is invalid; in practice
    the Rust code never returns an error from individual operations (the "removed all
    voters" check is done after the whole list). -/
def applyOne (cfg : Cfg) (prs : Prs) (c : Change) : Cfg × Prs :=
  if c.nodeId = 0 then (cfg, prs)   -- node_id = 0 is silently ignored
  else match c.changeType with
  | ChangeType.AddNode =>
    let cfg' := { cfg with
      incoming     := cfg.incoming.insert c.nodeId
      learners     := cfg.learners.erase c.nodeId
      learnersNext := cfg.learnersNext.erase c.nodeId }
    (cfg', prs.insert c.nodeId)
  | ChangeType.AddLearner =>
    if c.nodeId ∈ cfg.learners then (cfg, prs)   -- idempotent
    else
      -- demote from incoming; stage or directly promote
      let cfg1 := { cfg with
        incoming     := cfg.incoming.erase c.nodeId
        learners     := cfg.learners.erase c.nodeId
        learnersNext := cfg.learnersNext.erase c.nodeId }
      let cfg2 :=
        if c.nodeId ∈ cfg.outgoing
        then { cfg1 with learnersNext := cfg1.learnersNext.insert c.nodeId }
        else { cfg1 with learners     := cfg1.learners.insert c.nodeId }
      (cfg2, prs.insert c.nodeId)
  | ChangeType.RemoveNode =>
    if c.nodeId ∉ prs then (cfg, prs)            -- not tracked: no-op
    else
      let cfg' := { cfg with
        incoming     := cfg.incoming.erase c.nodeId
        learners     := cfg.learners.erase c.nodeId
        learnersNext := cfg.learnersNext.erase c.nodeId }
      -- Keep progress if still needed by the outgoing config
      let prs' := if c.nodeId ∈ cfg.outgoing then prs else prs.erase c.nodeId
      (cfg', prs')

/-- Apply a list of changes.  Returns `none` if the result would have no incoming voters. -/
def applyAll (cfg : Cfg) (prs : Prs) : List Change → Option (Cfg × Prs)
  | [] =>
    if cfg.incoming != ∅ then some (cfg, prs)
    else none   -- "removed all voters"
  | c :: cs =>
    let (cfg', prs') := applyOne cfg prs c
    applyAll cfg' prs' cs

/-- Model of `Changer::enter_joint`. -/
def enterJoint (cfg : Cfg) (prs : Prs) (autoLeave : Bool) (ccs : List Change)
    : Option (Cfg × Prs) :=
  if isJoint cfg then none                       -- already joint
  else if cfg.incoming == ∅ then none            -- can't joint from empty config
  else
    -- copy incoming → outgoing  (C_{new,old} construction)
    let cfg0 := { cfg with outgoing := cfg.incoming }
    -- apply changes to incoming
    match applyAll cfg0 prs ccs with
    | none => none
    | some (cfg1, prs1) =>
      some ({ cfg1 with autoLeave }, prs1)

/-- Model of `Changer::leave_joint`. -/
def leaveJoint (cfg : Cfg) (prs : Prs) : Option (Cfg × Prs) :=
  if !isJoint cfg then none              -- not joint
  else
    -- promote staged learners
    let cfg1 := { cfg with
      learners     := cfg.learners ∪ cfg.learnersNext
      learnersNext := ∅ }
    -- remove nodes that were only in outgoing
    let toRemove := cfg1.outgoing.filter
      (fun id => id ∉ cfg1.incoming ∧ id ∉ cfg1.learners)
    let prs'  := prs.filter (fun id => id ∉ toRemove)
    let cfg2  := { cfg1 with outgoing := ∅, autoLeave := false }
    some (cfg2, prs')

/-- Model of `Changer::simple` (no joint; at most one voter change). -/
def changerSimple (cfg : Cfg) (prs : Prs) (ccs : List Change)
    : Option (Cfg × Prs) :=
  if isJoint cfg then none
  else
    match applyAll cfg prs ccs with
    | none => none
    | some (cfg', prs') =>
      -- at most one voter changed (symmetric difference ≤ 1)
      let diff := (cfg'.incoming.card + cfg.incoming.card) -
                  2 * (cfg'.incoming ∩ cfg.incoming).card
      if diff > 1 then none
      else some (cfg', prs')

-- ---------------------------------------------------------------------------
-- Propositions
-- ---------------------------------------------------------------------------

-- ~~~ Invariant characterisation ~~~

/-- PROP-1  Incoming voters are tracked. -/
theorem inv_incoming_tracked (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    ∀ id ∈ cfg.incoming, id ∈ prs := h.1

/-- PROP-2  Outgoing voters are tracked. -/
theorem inv_outgoing_tracked (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    ∀ id ∈ cfg.outgoing, id ∈ prs := h.2.1

/-- PROP-3  Learners are tracked. -/
theorem inv_learners_tracked (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    ∀ id ∈ cfg.learners, id ∈ prs := h.2.2.1

/-- PROP-4  Learners and incoming voters are disjoint. -/
theorem inv_learners_incoming_disjoint (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    ∀ id, id ∈ cfg.learners → id ∉ cfg.incoming := h.2.2.2.1

/-- PROP-5  Learners and outgoing voters are disjoint. -/
theorem inv_learners_outgoing_disjoint (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    ∀ id, id ∈ cfg.learners → id ∉ cfg.outgoing := h.2.2.2.2.1

/-- PROP-6  learnersNext nodes are tracked. -/
theorem inv_learnersNext_tracked (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    ∀ id ∈ cfg.learnersNext, id ∈ prs := h.2.2.2.2.2.1

/-- PROP-7  learnersNext ⊆ outgoing (staging invariant). -/
theorem inv_learnersNext_subset_outgoing (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    ∀ id ∈ cfg.learnersNext, id ∈ cfg.outgoing := h.2.2.2.2.2.2.1

/-- PROP-8  Non-joint: learnersNext = ∅. -/
theorem inv_nonjoint_learnersNext_empty (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    isJoint cfg = false → cfg.learnersNext = ∅ :=
  fun hj => (h.2.2.2.2.2.2.2 hj).1

/-- PROP-9  Non-joint: autoLeave = false. -/
theorem inv_nonjoint_autoLeave_false (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    isJoint cfg = false → cfg.autoLeave = false :=
  fun hj => (h.2.2.2.2.2.2.2 hj).2

/-- PROP-10  incoming ∩ learners = ∅ (Finset version of PROP-4). -/
theorem voters_learners_disjoint (cfg : Cfg) (prs : Prs) (h : Inv cfg prs) :
    cfg.incoming ∩ cfg.learners = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro id
  simp only [Finset.mem_inter, not_and]
  intro hmem_in
  intro hmem_learn
  exact h.2.2.2.1 id hmem_learn hmem_in

-- ~~~ enterJoint structural results ~~~

/-- PROP-11  enterJoint fails if already joint. -/
theorem enter_joint_fails_if_joint (cfg : Cfg) (prs : Prs) (autoLeave : Bool)
    (ccs : List Change) (h : isJoint cfg = true) :
    enterJoint cfg prs autoLeave ccs = none := by
  simp [enterJoint, h]

/-- PROP-12  enterJoint fails if incoming is empty. -/
theorem enter_joint_fails_if_empty_incoming (cfg : Cfg) (prs : Prs) (autoLeave : Bool)
    (ccs : List Change) (hj : isJoint cfg = false) (he : cfg.incoming = ∅) :
    enterJoint cfg prs autoLeave ccs = none := by
  simp [enterJoint, hj, he]

/-- PROP-13  On success, enterJoint produces a joint config. -/
theorem enter_joint_result_is_joint (cfg : Cfg) (prs : Prs) (autoLeave : Bool)
    (ccs : List Change) (cfg' : Cfg) (prs' : Prs)
    (h : enterJoint cfg prs autoLeave ccs = some (cfg', prs')) :
    isJoint cfg' = true := by
  sorry

/-- PROP-14  With empty ccs, enterJoint's outgoing = original incoming. -/
theorem enter_joint_empty_ccs_outgoing (cfg : Cfg) (prs : Prs) (autoLeave : Bool)
    (cfg' : Cfg) (prs' : Prs)
    (hj : isJoint cfg = false) (hn : cfg.incoming ≠ ∅)
    (h : enterJoint cfg prs autoLeave [] = some (cfg', prs')) :
    cfg'.outgoing = cfg.incoming := by
  sorry

/-- PROP-15  enterJoint preserves incoming voters (empty ccs). -/
theorem enter_joint_preserves_incoming_empty_ccs (cfg : Cfg) (prs : Prs) (autoLeave : Bool)
    (cfg' : Cfg) (prs' : Prs)
    (hj : isJoint cfg = false) (hn : cfg.incoming ≠ ∅)
    (h : enterJoint cfg prs autoLeave [] = some (cfg', prs')) :
    cfg'.incoming = cfg.incoming := by
  sorry

/-- PROP-16  If enterJoint succeeds, leaveJoint will succeed on the result. -/
theorem enter_leave_joint_possible (cfg : Cfg) (prs : Prs) (autoLeave : Bool)
    (ccs : List Change) (cfg' : Cfg) (prs' : Prs)
    (h : enterJoint cfg prs autoLeave ccs = some (cfg', prs')) :
    ∃ cfg'' prs'', leaveJoint cfg' prs' = some (cfg'', prs'') := by
  sorry

-- ~~~ leaveJoint structural results ~~~

/-- PROP-17  leaveJoint fails if not joint. -/
theorem leave_joint_fails_if_not_joint (cfg : Cfg) (prs : Prs)
    (h : isJoint cfg = false) :
    leaveJoint cfg prs = none := by
  simp [leaveJoint, h]

/-- PROP-19  leaveJoint clears outgoing. -/
theorem leave_joint_outgoing_empty (cfg : Cfg) (prs : Prs)
    (cfg' : Cfg) (prs' : Prs)
    (h : leaveJoint cfg prs = some (cfg', prs')) :
    cfg'.outgoing = ∅ := by
  sorry

/-- PROP-18  leaveJoint produces a non-joint config. -/
theorem leave_joint_not_joint (cfg : Cfg) (prs : Prs)
    (cfg' : Cfg) (prs' : Prs)
    (h : leaveJoint cfg prs = some (cfg', prs')) :
    isJoint cfg' = false := by
  have hout := leave_joint_outgoing_empty cfg prs cfg' prs' h
  simp [isJoint, hout]

/-- PROP-20  leaveJoint clears learnersNext (all staged learners promoted). -/
theorem leave_joint_learnersNext_empty (cfg : Cfg) (prs : Prs)
    (cfg' : Cfg) (prs' : Prs)
    (h : leaveJoint cfg prs = some (cfg', prs')) :
    cfg'.learnersNext = ∅ := by
  sorry

/-- PROP-21  leaveJoint sets autoLeave = false. -/
theorem leave_joint_autoLeave_false (cfg : Cfg) (prs : Prs)
    (cfg' : Cfg) (prs' : Prs)
    (h : leaveJoint cfg prs = some (cfg', prs')) :
    cfg'.autoLeave = false := by
  sorry

/-- PROP-22  Nodes in learnersNext before leaveJoint are in learners after. -/
theorem leave_joint_promotes_learnersNext (cfg : Cfg) (prs : Prs)
    (cfg' : Cfg) (prs' : Prs)
    (h : leaveJoint cfg prs = some (cfg', prs')) :
    ∀ id ∈ cfg.learnersNext, id ∈ cfg'.learners := by
  sorry

/-- PROP-23  applyOne with AddNode makes id ∈ incoming. -/
theorem applyOne_addNode_in_incoming (cfg : Cfg) (prs : Prs) (id : NodeId) (hid : id ≠ 0) :
    id ∈ (applyOne cfg prs ⟨id, ChangeType.AddNode⟩).1.incoming := by
  simp [applyOne, hid]

/-- PROP-24  applyOne with RemoveNode removes id from incoming (when tracked). -/
theorem applyOne_removeNode_not_in_incoming (cfg : Cfg) (prs : Prs) (id : NodeId)
    (hid : id ≠ 0) (hprs : id ∈ prs) :
    id ∉ (applyOne cfg prs ⟨id, ChangeType.RemoveNode⟩).1.incoming := by
  simp [applyOne, hid, hprs, Finset.not_mem_erase]

/-- PROP-25  leaveJoint: incoming voters are unchanged. -/
theorem leave_joint_incoming_unchanged (cfg : Cfg) (prs : Prs)
    (cfg' : Cfg) (prs' : Prs)
    (h : leaveJoint cfg prs = some (cfg', prs')) :
    cfg'.incoming = cfg.incoming := by
  sorry

/-- PROP-26  changerSimple fails if config is joint. -/
theorem simple_fails_if_joint (cfg : Cfg) (prs : Prs) (ccs : List Change)
    (h : isJoint cfg = true) :
    changerSimple cfg prs ccs = none := by
  simp [changerSimple, h]

-- ~~~ Round-trip example ~~~

/-- Example round-trip: start with cfg {incoming={1,2,3}, outgoing=∅, …},
    enter_joint with empty changes, leave_joint — outgoing is empty again. -/
example :
    let cfg₀ : Cfg := ⟨{1, 2, 3}, ∅, ∅, ∅, false⟩
    let prs₀ : Prs := {1, 2, 3}
    ∃ cfg₁ prs₁ cfg₂ prs₂,
      enterJoint cfg₀ prs₀ false [] = some (cfg₁, prs₁) ∧
      leaveJoint cfg₁ prs₁ = some (cfg₂, prs₂) ∧
      cfg₂.outgoing = ∅ := by
  native_decide

/-- enterJoint with empty ccs produces the expected intermediate config. -/
#eval
  let cfg₀ : Cfg := ⟨{1, 2, 3}, ∅, ∅, ∅, false⟩
  let prs₀ : Prs := {1, 2, 3}
  enterJoint cfg₀ prs₀ false []

/-- leaveJoint on the joint config produces a clean non-joint config. -/
#eval
  let cfg₁ : Cfg := ⟨{1, 2, 3}, {1, 2, 3}, ∅, ∅, false⟩
  let prs₁ : Prs := {1, 2, 3}
  leaveJoint cfg₁ prs₁

end FVSquad.ConfChanger
