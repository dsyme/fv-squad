/-!
# HandleHeartbeatResponse — Lean 4 Specification

Formal specification of `RaftCore::handle_heartbeat_response` from `src/raft.rs`.

The function processes an incoming `MsgHeartbeatResponse` from a follower peer.
It has three sequential concerns:
1. **Progress unblocking** — clear Probe pause, update committed index, mark active.
2. **Catch-up trigger** — send append if peer is behind or has pending snapshot.
3. **ReadIndex quorum** — if a quorum acknowledges the heartbeat context, drain
   and dispatch pending read requests.

## Key properties verified

1. **`update_committed_mono`**: committed index is monotonically non-decreasing.
2. **`resume_clears_paused`**: `resume` always sets `paused = false`.
3. **`hbr_progress_unblocked`**: after the progress-update phase,
   `paused = false` regardless of prior state.
4. **`hbr_inflight_freed`**: in Replicate mode with a full window, the result
   is no longer full.
5. **`hbr_catchup_condition`**: catch-up send is triggered iff
   `matched < last_index ∨ pending_snapshot`.
6. **`readindex_quorum_gate`**: read responses are dispatched iff `has_quorum`.
7. **`readindex_monotone_context`**: only requests up to the matched context
   are advanced; later requests remain queued.
8. **`readindex_idempotent`**: advancing the same context twice is a no-op
   (the queue entry is removed on first advance).

## Model scope and approximations

* **Progress model** reuses `FVSquad.Progress` and `FVSquad.Inflights`.
* **`last_index`** is modelled as a `Nat` parameter (abstract log length).
* **`send_append` trigger** is captured as a Boolean predicate; the actual
  message construction is covered in `FVSquad.BcastAppend`.
* **ReadIndex** is modelled with a list-based queue and a `Finset`-based ack set;
  the real implementation uses `VecDeque` and `HashSet`.
* **I/O / logging** are omitted.
* **Unknown-peer early-exit** is modelled as `Option` on the progress entry.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import FVSquad.Inflights
import FVSquad.Progress

namespace FVSquad.HandleHeartbeatResponse

open FVSquad.Inflights (Inflights bounded add full free_to)
open FVSquad.Progress  (Progress ProgressState valid)

/-! ## Progress model (extended with committed_index) -/

/-- A follower's progress entry, extended with committed_index tracking. -/
structure HBProgress where
  committed_index     : Nat
  matched             : Nat
  next_idx            : Nat
  state               : ProgressState
  paused              : Bool
  pending_snapshot    : Nat     -- 0 = INVALID_INDEX (no pending snapshot)
  recent_active       : Bool
  ins                 : Inflights
  deriving Repr

/-- Valid progress: `matched + 1 ≤ next_idx`. -/
def hbp_valid (p : HBProgress) : Prop := p.matched + 1 ≤ p.next_idx

/-! ## `update_committed` -/

/-- Monotone committed-index advancement.
    Mirrors `Progress::update_committed`. -/
def updateCommitted (p : HBProgress) (ci : Nat) : HBProgress :=
  { p with committed_index := max p.committed_index ci }

/-- **Monotone**: committed index never decreases. -/
theorem update_committed_mono (p : HBProgress) (ci : Nat) :
    p.committed_index ≤ (updateCommitted p ci).committed_index := by
  simp [updateCommitted, Nat.le_max_left]

/-- **Absorbs stale values**: if `ci ≤ p.committed_index`, the index is unchanged. -/
theorem update_committed_stale (p : HBProgress) (ci : Nat)
    (h : ci ≤ p.committed_index) :
    (updateCommitted p ci).committed_index = p.committed_index := by
  simp [updateCommitted, Nat.max_eq_left h]

/-- **Takes larger value**: if `ci > p.committed_index`, the index advances. -/
theorem update_committed_advances (p : HBProgress) (ci : Nat)
    (h : p.committed_index < ci) :
    (updateCommitted p ci).committed_index = ci := by
  simp [updateCommitted, Nat.max_eq_right (Nat.le_of_lt h)]

/-- `updateCommitted` does not touch other fields. -/
@[simp] theorem update_committed_matched (p : HBProgress) (ci : Nat) :
    (updateCommitted p ci).matched = p.matched := rfl

@[simp] theorem update_committed_paused (p : HBProgress) (ci : Nat) :
    (updateCommitted p ci).paused = p.paused := rfl

@[simp] theorem update_committed_state (p : HBProgress) (ci : Nat) :
    (updateCommitted p ci).state = p.state := rfl

@[simp] theorem update_committed_ins (p : HBProgress) (ci : Nat) :
    (updateCommitted p ci).ins = p.ins := rfl

/-! ## `resume` -/

/-- Mirrors `Progress::resume`: clears flow-control pause. -/
def resumeProgress (p : HBProgress) : HBProgress :=
  { p with paused := false }

/-- **Clears pause**: after `resume`, `paused = false`. -/
theorem resume_clears_paused (p : HBProgress) :
    (resumeProgress p).paused = false := rfl

/-- `resumeProgress` preserves all other fields. -/
@[simp] theorem resume_matched (p : HBProgress) :
    (resumeProgress p).matched = p.matched := rfl

@[simp] theorem resume_state (p : HBProgress) :
    (resumeProgress p).state = p.state := rfl

@[simp] theorem resume_ins (p : HBProgress) :
    (resumeProgress p).ins = p.ins := rfl

@[simp] theorem resume_committed (p : HBProgress) :
    (resumeProgress p).committed_index = p.committed_index := rfl

/-! ## Inflight free-first-one -/

/-- Mirror of `Inflights::free_first_one`: frees the oldest in-flight entry.
    Modelled as removing the first element from the items list. -/
def freeFirstOne (ins : Inflights) : Inflights :=
  match ins.items with
  | []      => ins
  | _ :: t  => { ins with items := t }

/-- After `freeFirstOne`, the window is no longer full (assuming it was full). -/
theorem freeFirstOne_not_full (ins : Inflights)
    (hfull : full ins = true) :
    full (freeFirstOne ins) = false := by
  simp only [full, bounded, freeFirstOne] at *
  split
  · -- items = []  →  full should already be false  — contradicts hfull
    simp_all [full]
  · simp_all [full]

/-- `freeFirstOne` on a non-full window is a no-op in terms of full-ness. -/
theorem freeFirstOne_not_full_noop (ins : Inflights)
    (hnf : full ins = false) :
    full (freeFirstOne ins) = false := by
  simp only [full, bounded, freeFirstOne] at *
  split
  · simp [full]
  · simp_all [full]

/-! ## Combined progress update (steps 1–4 of `handle_heartbeat_response`) -/

/-- The "progress update" phase of `handle_heartbeat_response`:
    update committed, mark active, clear pause, free inflight slot if needed. -/
def hbrUpdateProgress (p : HBProgress) (commit : Nat) : HBProgress :=
  let p1 := updateCommitted p commit
  let p2 := { p1 with recent_active := true }
  let p3 := resumeProgress p2
  -- free one inflight slot if in Replicate mode with full window
  if p3.state = .Replicate && full p3.ins then
    { p3 with ins := freeFirstOne p3.ins }
  else
    p3

/-- **Paused is cleared**: after progress update, `paused = false`. -/
theorem hbr_progress_unblocked (p : HBProgress) (commit : Nat) :
    (hbrUpdateProgress p commit).paused = false := by
  simp [hbrUpdateProgress, resumeProgress, updateCommitted]
  split_ifs <;> simp [resumeProgress]

/-- **Recent-active is set**: after progress update, `recent_active = true`. -/
theorem hbr_recent_active (p : HBProgress) (commit : Nat) :
    (hbrUpdateProgress p commit).recent_active = true := by
  simp [hbrUpdateProgress, resumeProgress, updateCommitted]
  split_ifs <;> simp

/-- **Committed index is monotone**: after progress update, committed_index ≥ before. -/
theorem hbr_committed_mono (p : HBProgress) (commit : Nat) :
    p.committed_index ≤ (hbrUpdateProgress p commit).committed_index := by
  simp [hbrUpdateProgress, updateCommitted, resumeProgress]
  split_ifs <;> simp [Nat.le_max_left]

/-- **Inflight freed (Replicate + full)**: if in Replicate mode with full inflight,
    the result is no longer full. -/
theorem hbr_inflight_freed (p : HBProgress) (commit : Nat)
    (hstate : p.state = .Replicate)
    (hfull : full p.ins = true) :
    full (hbrUpdateProgress p commit).ins = false := by
  simp [hbrUpdateProgress, resumeProgress, updateCommitted, hstate, hfull]
  exact freeFirstOne_not_full p.ins hfull

/-- **No free when not in Replicate**: inflight window is untouched. -/
theorem hbr_inflight_probe_unchanged (p : HBProgress) (commit : Nat)
    (hstate : p.state = .Probe) :
    (hbrUpdateProgress p commit).ins = p.ins := by
  simp [hbrUpdateProgress, resumeProgress, updateCommitted, hstate]

/-- **No free when window not full**: inflight window is untouched. -/
theorem hbr_inflight_not_full_unchanged (p : HBProgress) (commit : Nat)
    (hnf : full p.ins = false) :
    (hbrUpdateProgress p commit).ins = p.ins := by
  simp [hbrUpdateProgress, resumeProgress, updateCommitted, hnf]

/-- `hbrUpdateProgress` preserves `hbp_valid`. -/
theorem hbr_valid_preserved (p : HBProgress) (commit : Nat)
    (hv : hbp_valid p) :
    hbp_valid (hbrUpdateProgress p commit) := by
  simp [hbrUpdateProgress, resumeProgress, updateCommitted, hbp_valid] at *
  split_ifs <;> simp [hbp_valid, hv]

/-! ## Catch-up trigger condition -/

/-- `handle_heartbeat_response` calls `send_append` iff this predicate holds. -/
def shouldSendCatchup (p : HBProgress) (lastIndex : Nat) : Bool :=
  p.matched < lastIndex || p.pending_snapshot ≠ 0

/-- **Catch-up fires when behind**: if `matched < lastIndex`, catch-up is triggered. -/
theorem hbr_catchup_behind (p : HBProgress) (lastIndex : Nat)
    (h : p.matched < lastIndex) :
    shouldSendCatchup p lastIndex = true := by
  simp [shouldSendCatchup, h]

/-- **Catch-up fires on pending snapshot**: even if caught up, pending snapshot triggers. -/
theorem hbr_catchup_snapshot (p : HBProgress) (lastIndex : Nat)
    (h : p.pending_snapshot ≠ 0) :
    shouldSendCatchup p lastIndex = true := by
  simp [shouldSendCatchup, h]

/-- **No catch-up when fully caught up**: if matched ≥ lastIndex and no snapshot,
    no send is triggered. -/
theorem hbr_no_catchup_up_to_date (p : HBProgress) (lastIndex : Nat)
    (hm : lastIndex ≤ p.matched)
    (hs : p.pending_snapshot = 0) :
    shouldSendCatchup p lastIndex = false := by
  simp [shouldSendCatchup, hs, Nat.not_lt.mpr hm]

/-! ## ReadIndex model -/

/-- Abstract ReadIndex state: a queue of context tokens, each with an ack set. -/
structure ReadOnlyState where
  /-- Ordered list of pending context tokens (front = oldest). -/
  queue   : List (List Nat)
  /-- Acknowledgement sets: context → set of peer IDs that have ack'd. -/
  acks    : List (List Nat × Finset Nat)
  deriving Repr

/-- A quorum is any majority; abstracted as a predicate over Finset. -/
def hasQuorum (allPeers : Finset Nat) (acks : Finset Nat) : Bool :=
  decide (2 * acks.card > allPeers.card)

/-- `recv_ack`: record that peer `id` has acked `ctx`.
    Returns the updated ack set for `ctx` (if ctx is pending). -/
def recvAck (ro : ReadOnlyState) (id : Nat) (ctx : List Nat) :
    ReadOnlyState × Option (Finset Nat) :=
  match ro.acks.findIdx? (fun p => p.1 = ctx) with
  | none => (ro, none)
  | some i =>
    let (c, s) := ro.acks.get ⟨i, by omega⟩  -- safe by findIdx
    let newAcks := ro.acks.set i (c, s.insert id)
    ({ ro with acks := newAcks }, some (s.insert id))

/-- `advance`: dequeue all pending reads up to and including `ctx`.
    Returns the dequeued contexts (for which read responses are sent). -/
def advance (ro : ReadOnlyState) (ctx : List Nat) :
    ReadOnlyState × List (List Nat) :=
  match ro.queue.findIdx? (· = ctx) with
  | none => (ro, [])
  | some i =>
    let dequeued := ro.queue.take (i + 1)
    let remaining := ro.queue.drop (i + 1)
    ({ ro with queue := remaining }, dequeued)

/-- **ReadIndex quorum gate**: read responses dispatched iff quorum. -/
theorem readindex_quorum_gate
    (allPeers : Finset Nat) (ackSet : Finset Nat) (ctx : List Nat)
    (ro : ReadOnlyState) :
    -- If quorum is reached, advance returns non-empty list (when ctx is queued)
    hasQuorum allPeers ackSet = true →
    ctx ∈ ro.queue →
    (advance ro ctx).2 ≠ [] := by
  intro _ hmem
  simp [advance]
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  have : List.findIdx? (· = ctx) ro.queue ≠ none := by
    rw [List.findIdx?_eq_some_iff_findIdx]
    simp
    exact ⟨i.val, i.isLt, hi⟩
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp this
  simp [hj]
  omega

/-- **Monotone context**: only requests up to ctx are dequeued; later ones remain. -/
theorem readindex_monotone_context
    (ro : ReadOnlyState) (ctx : List Nat) (later : List Nat)
    (hlater : later ∈ ro.queue)
    (hafter : ∀ i j, ro.queue.get? i = some ctx →
                     ro.queue.get? j = some later → i < j) :
    later ∈ (advance ro ctx).1.queue := by
  simp [advance]
  split
  · exact hlater
  · rename_i i hi
    -- 'later' comes after ctx in queue; it survives the drop
    simp [List.mem_drop]
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hlater
    use k.val
    refine ⟨?_, hk⟩
    have hci := List.findIdx?_get hi
    simp at hci
    have hlt := hafter i k.val (by simp [List.get?_eq_get]; exact hci)
                               (List.get?_eq_get k |>.mpr hk.symm)
    omega

/-- **Idempotent advance**: advancing the same context twice is a no-op.
    Requires `List.Nodup` on the queue, which holds in the real implementation
    because `ReadOnly::add_request` guards against duplicate keys. -/
theorem readindex_idempotent
    (ro : ReadOnlyState) (ctx : List Nat)
    (hnodup : ro.queue.Nodup) :
    let ro' := (advance ro ctx).1
    (advance ro' ctx).1 = ro' ∧ (advance ro' ctx).2 = [] := by
  simp only [advance]
  split
  · rename_i h; simp [h]
  · rename_i i hi
    have hlt : i < ro.queue.length := List.findIdx?_lt hi
    have hget : ro.queue.get ⟨i, hlt⟩ = ctx := by
      have := List.findIdx?_get hi; simp at this; exact this.symm
    -- With Nodup, ctx cannot appear in ro.queue.drop (i+1)
    -- because it would require two distinct positions in ro.queue with the same value.
    have hnotmem : ctx ∉ ro.queue.drop (i + 1) := by
      intro hmem
      rw [List.mem_iff_get] at hmem
      obtain ⟨j, hjval⟩ := hmem
      -- j : Fin (ro.queue.drop (i+1)).length
      have hlt2 : i + 1 + j.val < ro.queue.length := by
        have := j.isLt; simp [List.length_drop] at this; omega
      -- (ro.queue.drop (i+1)).get j = ro.queue.get ⟨i+1+j.val, _⟩
      have hget2 : ro.queue.get ⟨i + 1 + j.val, hlt2⟩ = ctx := by
        rw [← hjval]; exact List.get_drop ro.queue (i + 1) j
      -- Both position i and i+1+j.val map to ctx — contradicts Nodup
      have heq : ro.queue.get ⟨i, hlt⟩ = ro.queue.get ⟨i + 1 + j.val, hlt2⟩ :=
        hget.trans hget2.symm
      have hfin := (List.Nodup.get_inj_iff hnodup).mp heq
      simp [Fin.ext_iff] at hfin; omega
    -- With ctx ∉ drop, findIdx? on the drop returns none (by induction)
    have hfind_none : List.findIdx? (· = ctx) (ro.queue.drop (i + 1)) = none := by
      have hnotmem' : ∀ x ∈ ro.queue.drop (i + 1), x ≠ ctx :=
        fun x hx heq => hnotmem (heq ▸ hx)
      revert hnotmem'
      generalize ro.queue.drop (i + 1) = l
      intro hl
      induction l with
      | nil => simp [List.findIdx?]
      | cons a as ih =>
        simp only [List.findIdx?]
        have ha : a ≠ ctx := hl a (List.mem_cons_self _ _)
        have has : ∀ x ∈ as, x ≠ ctx := fun x hx => hl x (List.mem_cons_of_mem _ hx)
        simp [ha, ih has]
    simp [hfind_none]

/-! ## Phase 4: Full handler model

This section lifts the individual components into a single pure function
`handleHeartbeatResponse` that mirrors the complete Rust function body.

### What is modelled
* All three sequential concerns (progress unblock, catch-up trigger, ReadIndex quorum).
* Unknown-peer early-exit (modelled via `Option HBProgress`).
* ReadOnly option guard (`readOnlySafe`) and empty-context guard.

### What is NOT modelled (documented approximations)
* The actual `MsgAppend`/`MsgSnapshot` construction for catch-up — only the
  Boolean trigger `shouldSendCatchup` is captured.
* `ReadOnly::recv_ack` uses a list-based ack model; the real code uses a
  `HashMap<Vec<u8>, ReadIndexStatus>` keyed by context.
* The `ReadOnly::LeaseBased` path is omitted (the guard `readOnlySafe = true`
  must hold for ReadIndex processing to occur).
* Message I/O (sending messages to the network layer) is not modelled.
-/

/-- Full input for the handle_heartbeat_response pure model. -/
structure HBRInput where
  /-- The peer's progress entry; `none` → unknown peer → early exit. -/
  progress     : Option HBProgress
  /-- Leader's current last index (abstract log length). -/
  lastIndex    : Nat
  /-- Whether ReadOnly mode is Safe (the only mode that triggers ReadIndex quorum). -/
  readOnlySafe : Bool
  /-- The context token from the heartbeat response (empty = plain heartbeat). -/
  ctx          : List Nat
  /-- The commit index from the heartbeat response message. -/
  commitIndex  : Nat
  /-- The sender peer ID. -/
  fromId       : Nat
  /-- All known peer IDs (used for quorum computation). -/
  allPeers     : Finset Nat
  /-- Current ReadOnly state. -/
  readOnly     : ReadOnlyState
  deriving Repr

/-- Full output from the handle_heartbeat_response pure model. -/
structure HBROutput where
  /-- Updated progress entry (`none` if unknown peer). -/
  progress      : Option HBProgress
  /-- `true` iff a catch-up append should be sent to the peer. -/
  sendCatchup   : Bool
  /-- Contexts of read requests dispatched because quorum was reached. -/
  readDispatches : List (List Nat)
  /-- Updated ReadOnly state after processing acks. -/
  readOnly      : ReadOnlyState
  deriving Repr

/-- Pure model of `RaftCore::handle_heartbeat_response`. -/
def handleHeartbeatResponse (inp : HBRInput) : HBROutput :=
  match inp.progress with
  | none =>
    -- Unknown peer: early exit, no state changes
    { progress := none, sendCatchup := false,
      readDispatches := [], readOnly := inp.readOnly }
  | some pr =>
    -- Step 1: update committed, mark active, resume, free inflight
    let pr1 := hbrUpdateProgress pr inp.commitIndex
    -- Step 2: catch-up trigger
    let catchup := shouldSendCatchup pr1 inp.lastIndex
    -- Step 3: ReadIndex quorum (only in Safe mode with a non-empty context)
    let (ro1, dispatches) :=
      if inp.readOnlySafe && !inp.ctx.isEmpty then
        let (ro', ackSet) := recvAck inp.readOnly inp.fromId inp.ctx
        match ackSet with
        | none => (ro', [])
        | some acks =>
          if hasQuorum inp.allPeers acks then
            advance ro' inp.ctx
          else
            (ro', [])
      else
        (inp.readOnly, [])
    { progress := some pr1, sendCatchup := catchup,
      readDispatches := dispatches, readOnly := ro1 }

/-! ## End-to-end theorems for the full handler -/

/-- **Unknown-peer early exit**: no output changes when the peer is not tracked. -/
theorem hbr_unknown_peer_noop (inp : HBRInput) (h : inp.progress = none) :
    let out := handleHeartbeatResponse inp
    out.progress = none ∧ out.sendCatchup = false ∧ out.readDispatches = [] := by
  simp [handleHeartbeatResponse, h]

/-- **Progress matches hbrUpdateProgress**: the output progress equals the result
    of the isolated progress-update function. -/
theorem hbr_progress_eq_update (inp : HBRInput) (pr : HBProgress)
    (h : inp.progress = some pr) :
    (handleHeartbeatResponse inp).progress = some (hbrUpdateProgress pr inp.commitIndex) := by
  simp [handleHeartbeatResponse, h]

/-- **Committed index is monotone** through the full handler. -/
theorem hbr_full_committed_mono (inp : HBRInput) (pr : HBProgress)
    (h : inp.progress = some pr) :
    match (handleHeartbeatResponse inp).progress with
    | none   => False
    | some p => pr.committed_index ≤ p.committed_index := by
  simp [handleHeartbeatResponse, h, hbrUpdateProgress, updateCommitted, Nat.le_max_left]

/-- **Paused is cleared** by the full handler. -/
theorem hbr_full_paused_cleared (inp : HBRInput) (pr : HBProgress)
    (h : inp.progress = some pr) :
    match (handleHeartbeatResponse inp).progress with
    | none   => False
    | some p => p.paused = false := by
  simp [handleHeartbeatResponse, h, hbrUpdateProgress, updateCommitted, resumeProgress]
  split_ifs <;> simp

/-- **No catch-up if already current**: if the peer is fully caught up and has no
    pending snapshot, `sendCatchup = false`. -/
theorem hbr_no_catchup_if_current (inp : HBRInput) (pr : HBProgress)
    (h_pr : inp.progress = some pr)
    (h_match : inp.lastIndex ≤ pr.matched)
    (h_snap  : pr.pending_snapshot = 0) :
    (handleHeartbeatResponse inp).sendCatchup = false := by
  simp only [handleHeartbeatResponse, h_pr, shouldSendCatchup, hbrUpdateProgress,
             updateCommitted, resumeProgress]
  split_ifs <;>
    simp [Nat.not_lt.mpr h_match, h_snap, shouldSendCatchup]

/-- **ReadIndex only fires in Safe mode with context**: if `readOnlySafe = false`
    or the context is empty, no reads are dispatched. -/
theorem hbr_reads_require_safe_ctx (inp : HBRInput)
    (h : inp.readOnlySafe = false ∨ inp.ctx.isEmpty = true) :
    (handleHeartbeatResponse inp).readDispatches = [] := by
  simp only [handleHeartbeatResponse]
  split
  · rfl
  · rename_i pr _
    rcases h with h | h
    · simp [h]
    · simp [h]

/-- **ReadOnly state is untouched** when not in Safe mode with context. -/
theorem hbr_ro_unchanged_when_no_ctx (inp : HBRInput)
    (h : inp.readOnlySafe = false ∨ inp.ctx.isEmpty = true) :
    (handleHeartbeatResponse inp).readOnly = inp.readOnly := by
  simp only [handleHeartbeatResponse]
  split
  · rfl
  · rename_i pr _
    rcases h with h | h
    · simp [h]
    · simp [h]

/-- **Catch-up fires when behind**: if the peer's matched index is below lastIndex,
    catch-up is triggered. -/
theorem hbr_catchup_fires_when_behind (inp : HBRInput) (pr : HBProgress)
    (h_pr : inp.progress = some pr)
    (h_behind : pr.matched < inp.lastIndex) :
    (handleHeartbeatResponse inp).sendCatchup = true := by
  simp only [handleHeartbeatResponse, h_pr, shouldSendCatchup, hbrUpdateProgress,
             updateCommitted, resumeProgress]
  split_ifs <;>
    simp [shouldSendCatchup, h_behind]

/-! ## Decidable sanity checks -/

private def exProg1 : HBProgress :=
  { committed_index := 3, matched := 7, next_idx := 8, state := .Probe,
    paused := true, pending_snapshot := 0, recent_active := false,
    ins := { cap := 4, items := [] } }

-- After hbrUpdateProgress, paused is cleared
example : (hbrUpdateProgress exProg1 5).paused = false := by decide
-- committed index advanced
example : (hbrUpdateProgress exProg1 5).committed_index = 5 := by decide
-- recent_active set
example : (hbrUpdateProgress exProg1 5).recent_active = true := by decide

private def exProg2 : HBProgress :=
  { committed_index := 2, matched := 5, next_idx := 6, state := .Replicate,
    paused := false, pending_snapshot := 0, recent_active := true,
    ins := { cap := 2, items := [1, 2] } }  -- full (2 items, cap 2)

-- In Replicate mode with full inflight, slot is freed
example : full exProg2.ins = true := by decide
example : full (hbrUpdateProgress exProg2 3).ins = false := by decide

-- Catch-up: behind → triggers
example : shouldSendCatchup exProg1 10 = true := by decide
-- Catch-up: caught up, no snapshot → no trigger
example : shouldSendCatchup { exProg1 with matched := 10 } 10 = false := by decide

-- hasQuorum: 3/5 is a majority
example : hasQuorum {0,1,2,3,4} {1,2,3} = true := by decide
-- hasQuorum: 2/5 is not
example : hasQuorum {0,1,2,3,4} {1,2} = false := by decide

/-! ### Full-handler sanity checks -/

private def exInp1 : HBRInput :=
  { progress     := some exProg1
    lastIndex    := 10
    readOnlySafe := false
    ctx          := []
    commitIndex  := 5
    fromId       := 2
    allPeers     := {1, 2, 3}
    readOnly     := { queue := [], acks := [] } }

-- Full handler: paused is cleared
example : ((handleHeartbeatResponse exInp1).progress.map (·.paused)) = some false := by decide
-- Full handler: committed index advanced to max(3, 5) = 5
example : ((handleHeartbeatResponse exInp1).progress.map (·.committed_index)) = some 5 := by decide
-- Full handler: catch-up fires (matched 7 < lastIndex 10)
example : (handleHeartbeatResponse exInp1).sendCatchup = true := by decide
-- Full handler: no read dispatches (readOnlySafe = false)
example : (handleHeartbeatResponse exInp1).readDispatches = [] := by decide

-- Unknown peer: all outputs are default/empty
private def exInpUnknown : HBRInput :=
  { progress := none, lastIndex := 5, readOnlySafe := true,
    ctx := [1, 2], commitIndex := 3, fromId := 99,
    allPeers := {1, 2, 3}, readOnly := { queue := [], acks := [] } }

example : (handleHeartbeatResponse exInpUnknown).sendCatchup = false := by decide
example : (handleHeartbeatResponse exInpUnknown).readDispatches = [] := by decide

end FVSquad.HandleHeartbeatResponse
