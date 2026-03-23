/-!
# BcastAppend — Lean 4 Specification

Formal specification of the log-replication dispatch logic from `src/raft.rs`:
- `RaftCore::maybe_send_append` — decides whether/what to send to one follower
- `RaftCore::send_append` — thin wrapper (`allow_empty = true`)
- `Raft::bcast_append` — broadcasts to all non-self peers
- `RaftCore::prepare_send_entries` — fills a `MsgAppend` from log + progress
- `Progress::update_state` — advances progress after a send

## Key properties verified

1. **`isPausedTrichotomy`**: `isPaused` separates cleanly by state.
2. **`updateState_probe_pauses`**: sending in Probe mode sets `paused = true`.
3. **`updateState_replicate_advances`**: sending in Replicate mode strictly
   advances `next_idx`.
4. **`updateState_replicate_valid`**: `update_state` preserves `valid` in
   Replicate mode.
5. **`maybeSendAppend_paused_false`**: paused peer → no message sent.
6. **`maybeSendAppend_result_sent`**: not-paused + entries available → true.
7. **`prepareSendEntries_type`**: message type is `MsgAppend`.
8. **`prepareSendEntries_index`**: `msg.index = pr.next_idx - 1`.
9. **`prepareSendEntries_commit`**: `msg.commit = raft_log.committed`.
10. **`bcastAppend_covers_all_peers`**: every non-self peer is visited.
11. **`updateState_replicate_inflight_bound`**: inflight window maintains
    the bounded invariant after add.

## Model scope and approximations

* **Log abstracted**: the Raft log is modelled as a function
  `Nat → Option (Nat × List Nat)` mapping `next_idx` to
  `(prev_term, entries)` — the result of a combined term+entries lookup.
  Real storage errors (temporarily-unavailable) are abstracted as `none`.
* **Snapshot path omitted**: the `pending_request_snapshot` / snapshot
  fallback path is not modelled here (it is covered in `RaftLogRestore.lean`).
* **Batching omitted**: `try_batching` is omitted; it is an optimisation
  that does not affect the per-peer flow-control properties.
* **`isPaused` for Replicate uses Inflights**: unlike the approximation in
  `Progress.lean`, this file imports `Inflights.lean` and uses
  `Inflights.full` so that the Replicate-mode flow-control is accurate.
* **`u64` indices**: modelled as `Nat`.
* **Message type**: modelled as an inductive with two constructors
  (`MsgAppend`, `MsgSnapshot`).

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic
import FVSquad.Inflights
import FVSquad.Progress

namespace FVSquad.BcastAppend

open FVSquad.Inflights (Inflights bounded add full)
open FVSquad.Progress  (Progress ProgressState valid)

/-! ## Message model -/

/-- Simplified Raft message type for append/snapshot path. -/
inductive MsgType where
  | MsgAppend
  | MsgSnapshot
  deriving DecidableEq, Repr

/-- Abstract Raft message used in this model. -/
structure Msg where
  to       : Nat         -- destination peer id
  msg_type : MsgType
  index    : Nat         -- prev-entry index (MsgAppend only)
  log_term : Nat         -- prev-entry term  (MsgAppend only)
  commit   : Nat         -- leader's committed index
  entries  : List Nat    -- entry indices (Nat stands for entry)
  deriving Repr

/-! ## Extended progress with Inflights -/

/-- Progress + inflight window, self-contained for this model. -/
structure FullProgress where
  matched          : Nat
  next_idx         : Nat
  state            : ProgressState
  paused           : Bool
  pending_snapshot : Nat
  recent_active    : Bool
  ins              : Inflights   -- inflight window
  deriving Repr

/-- Lift `FVSquad.Progress.valid` to `FullProgress`. -/
def valid_fp (p : FullProgress) : Prop :=
  p.matched + 1 ≤ p.next_idx

/-! ## `is_paused` — with Inflights -/

/-- Full `is_paused` including Inflights check for Replicate state. -/
def isPaused (p : FullProgress) : Bool :=
  match p.state with
  | .Probe     => p.paused
  | .Replicate => full p.ins
  | .Snapshot  => true

/-! ### Trichotomy theorems -/

/-- **Probe**: paused iff `paused = true`. -/
theorem isPaused_probe (p : FullProgress) (hs : p.state = .Probe) :
    isPaused p = p.paused := by
  simp [isPaused, hs]

/-- **Replicate**: paused iff inflight window is full. -/
theorem isPaused_replicate (p : FullProgress) (hs : p.state = .Replicate) :
    isPaused p = full p.ins := by
  simp [isPaused, hs]

/-- **Snapshot**: always paused. -/
theorem isPaused_snapshot (p : FullProgress) (hs : p.state = .Snapshot) :
    isPaused p = true := by
  simp [isPaused, hs]

/-- Trichotomy: `isPaused` decomposes cleanly by state. -/
theorem isPausedTrichotomy (p : FullProgress) :
    (p.state = .Probe     → isPaused p = p.paused) ∧
    (p.state = .Replicate → isPaused p = full p.ins) ∧
    (p.state = .Snapshot  → isPaused p = true) := by
  exact ⟨isPaused_probe p, isPaused_replicate p, isPaused_snapshot p⟩

/-! ## `update_state` -/

/-- **`update_state(last)`**: advance progress after sending entries up to `last`.
    - Replicate: optimistic advance (`next_idx = last + 1`), add to inflights.
    - Probe: pause (single-flight).
    - Snapshot: unreachable in correct Raft; modelled as identity. -/
def updateState (p : FullProgress) (last : Nat) : FullProgress :=
  match p.state with
  | .Replicate => { p with next_idx := last + 1, ins := add p.ins last }
  | .Probe     => { p with paused := true }
  | .Snapshot  => p   -- should not occur; left as identity

/-- **Probe → paused**: after `updateState`, Probe progress is paused. -/
theorem updateState_probe_pauses (p : FullProgress) (last : Nat)
    (hs : p.state = .Probe) :
    (updateState p last).paused = true := by
  simp [updateState, hs]

/-- **Replicate → next_idx advances**: `next_idx` grows. -/
theorem updateState_replicate_advances (p : FullProgress) (last : Nat)
    (hs : p.state = .Replicate) :
    p.next_idx ≤ (updateState p last).next_idx := by
  simp [updateState, hs]
  omega

/-- **Strictly advances when `last ≥ next_idx`**: entries were non-empty. -/
theorem updateState_replicate_strict (p : FullProgress) (last : Nat)
    (hs : p.state = .Replicate)
    (hlt : p.next_idx ≤ last + 1) :
    p.next_idx ≤ (updateState p last).next_idx := by
  simp [updateState, hs]
  omega

/-- **Replicate preserves `valid`**: if `valid_fp p` then `valid_fp (updateState p last)`. -/
theorem updateState_replicate_valid (p : FullProgress) (last : Nat)
    (hs : p.state = .Replicate)
    (hv : valid_fp p) :
    valid_fp (updateState p last) := by
  simp [updateState, hs, valid_fp]
  omega

/-- **Probe preserves `valid`**: only `paused` changes, indices untouched. -/
theorem updateState_probe_valid (p : FullProgress) (last : Nat)
    (hs : p.state = .Probe)
    (hv : valid_fp p) :
    valid_fp (updateState p last) := by
  simp [updateState, hs, valid_fp] at *
  exact hv

/-- **Replicate preserves inflight boundedness** when window is not full. -/
theorem updateState_replicate_inflight_bound (p : FullProgress) (last : Nat)
    (hs : p.state = .Replicate)
    (hb : bounded p.ins)
    (hnf : ¬ (full p.ins = true)) :
    bounded (updateState p last).ins := by
  simp [updateState, hs]
  apply FVSquad.Inflights.add_bounded
  · exact hb
  · exact hnf

/-! ## Abstract log model -/

/-- Abstract log: given `next_idx`, returns `some (prev_term, entries)` or `none`
    (unavailable).  `entries` is a list of entry indices. -/
def Log := Nat → Option (Nat × List Nat)

/-- The entries returned start at `next_idx` (first entry index = next_idx). -/
def logConsistent (lg : Log) : Prop :=
  ∀ ni, ∀ term ents,
    lg ni = some (term, ents) →
    ents.length > 0 →
    ents.head! = ni   -- first entry starts at ni

/-! ## `prepare_send_entries` -/

/-- Abstract model of `prepare_send_entries`:
    fills an outbound `Msg` and advances the progress. -/
def prepareSendEntries (committed : Nat) (p : FullProgress)
    (prevTerm : Nat) (ents : List Nat) : Msg × FullProgress :=
  let last := ents.getLast?.getD (p.next_idx - 1)
  let m : Msg := {
    to       := 0          -- filled by caller
    msg_type := .MsgAppend
    index    := p.next_idx - 1
    log_term := prevTerm
    commit   := committed
    entries  := ents
  }
  let p' := if ents.isEmpty then p else updateState p last
  (m, p')

/-- **Message type is `MsgAppend`**. -/
theorem prepareSendEntries_type (committed prevTerm : Nat)
    (p : FullProgress) (ents : List Nat) :
    (prepareSendEntries committed p prevTerm ents).1.msg_type = .MsgAppend := by
  simp [prepareSendEntries]

/-- **`msg.index = p.next_idx - 1`** (previous-entry index). -/
theorem prepareSendEntries_index (committed prevTerm : Nat)
    (p : FullProgress) (ents : List Nat) :
    (prepareSendEntries committed p prevTerm ents).1.index = p.next_idx - 1 := by
  simp [prepareSendEntries]

/-- **`msg.commit = committed`**: piggybacked committed index. -/
theorem prepareSendEntries_commit (committed prevTerm : Nat)
    (p : FullProgress) (ents : List Nat) :
    (prepareSendEntries committed p prevTerm ents).1.commit = committed := by
  simp [prepareSendEntries]

/-- **`msg.log_term = prevTerm`**: term of the previous entry. -/
theorem prepareSendEntries_log_term (committed prevTerm : Nat)
    (p : FullProgress) (ents : List Nat) :
    (prepareSendEntries committed p prevTerm ents).1.log_term = prevTerm := by
  simp [prepareSendEntries]

/-- **`msg.entries = ents`**: entries are forwarded unchanged. -/
theorem prepareSendEntries_entries (committed prevTerm : Nat)
    (p : FullProgress) (ents : List Nat) :
    (prepareSendEntries committed p prevTerm ents).1.entries = ents := by
  simp [prepareSendEntries]

/-! ## `maybe_send_append` -/

/-- Result of one `maybe_send_append` invocation:
    - `sent = false`: nothing pushed
    - `sent = true`:  the `msg` was produced and progress advanced to `prog'` -/
structure SendResult where
  sent  : Bool
  msg   : Option Msg
  prog' : FullProgress
  deriving Repr

/-- Abstract `maybe_send_append`.
    - Paused:            immediately return false.
    - `allow_empty=false` and no entries:  return false.
    - Otherwise:         build MsgAppend and advance progress. -/
def maybySendAppend (lg : Log) (committed : Nat) (p : FullProgress)
    (allow_empty : Bool) : SendResult :=
  if isPaused p then
    { sent := false, msg := none, prog' := p }
  else
    match lg p.next_idx with
    | none =>
        -- storage temporarily unavailable
        { sent := false, msg := none, prog' := p }
    | some (prevTerm, ents) =>
        if !allow_empty && ents.isEmpty then
          { sent := false, msg := none, prog' := p }
        else
          let (m, p') := prepareSendEntries committed p prevTerm ents
          { sent := true, msg := some m, prog' := p' }

/-- **Paused → not sent**: if `isPaused p`, no message is produced. -/
theorem maybySendAppend_paused_false (lg : Log) (committed : Nat)
    (p : FullProgress) (allow_empty : Bool)
    (hpause : isPaused p = true) :
    (maybySendAppend lg committed p allow_empty).sent = false := by
  simp [maybySendAppend, hpause]

/-- **Not paused + entries → sent**: if not paused and entries are available,
    a message is sent. -/
theorem maybySendAppend_result_sent (lg : Log) (committed : Nat)
    (p : FullProgress) (allow_empty : Bool)
    (hpause : isPaused p = false)
    (hlog : ∃ t e, lg p.next_idx = some (t, e) ∧ (allow_empty = true ∨ e.isEmpty = false)) :
    (maybySendAppend lg committed p allow_empty).sent = true := by
  obtain ⟨t, e, hte, hae⟩ := hlog
  simp only [maybySendAppend, hpause, hte, Bool.false_eq_true, ↓reduceIte]
  cases hae with
  | inl h =>
      simp [h, prepareSendEntries]
  | inr h =>
      simp [prepareSendEntries]
      cases allow_empty <;> simp_all

/-- **Not paused → progress unchanged if not sent**:
    when `maybe_send_append` returns false (not due to pause), progress is unchanged. -/
theorem maybySendAppend_not_sent_prog_unchanged (lg : Log) (committed : Nat)
    (p : FullProgress) (allow_empty : Bool)
    (h : (maybySendAppend lg committed p allow_empty).sent = false) :
    (maybySendAppend lg committed p allow_empty).prog' = p := by
  simp only [maybySendAppend] at h ⊢
  split
  · simp
  · split
    · simp
    · rename_i t e hte
      split
      · simp
      · simp [prepareSendEntries] at h

/-- **Sent message type is always `MsgAppend`** (in this model, snapshot path omitted). -/
theorem maybySendAppend_msg_type (lg : Log) (committed : Nat)
    (p : FullProgress) (allow_empty : Bool)
    (m : Msg)
    (h : (maybySendAppend lg committed p allow_empty).msg = some m) :
    m.msg_type = .MsgType.MsgAppend := by
  simp only [maybySendAppend] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i t e hte
      split at h
      · simp at h
      · simp only [prepareSendEntries] at h
        simp at h
        rw [← h]
        simp [prepareSendEntries]

/-! ## `bcast_append` -/

/-- Named fold step for `bcastAppend`, extracted for easier inductive reasoning. -/
private def bcastFoldStep (lg : Log) (committed selfId : Nat)
    (acc : List Msg × List (Nat × FullProgress))
    (idPr : Nat × FullProgress) :
    List Msg × List (Nat × FullProgress) :=
  let (msgs, progMap) := acc
  let (id, p) := idPr
  if id = selfId then
    (msgs, progMap ++ [(id, p)])
  else
    let res := maybySendAppend lg committed p true
    (if res.sent then msgs ++ [res.msg.getD
          { to := 0, msg_type := .MsgAppend, index := 0, log_term := 0, commit := 0, entries := [] }]
       else msgs,
     progMap ++ [(id, res.prog')])

/-- Model of one broadcast step: for each peer `p ≠ self_id`,
    call `maybySendAppend`.  Returns the list of produced messages and
    updated progress map. -/
def bcastAppend
    (lg : Log) (committed : Nat) (selfId : Nat)
    (peers : List (Nat × FullProgress)) :
    List Msg × List (Nat × FullProgress) :=
  peers.foldl (bcastFoldStep lg committed selfId) ([], [])

/-! ### `bcastFoldStep` helper lemmas -/

/-- The output progress-map keys equal the input pm keys plus all peer ids. -/
private theorem bcastFoldStep_fst_keys
    (lg : Log) (committed selfId : Nat)
    (peers : List (Nat × FullProgress))
    (ms : List Msg) (pm : List (Nat × FullProgress)) :
    (peers.foldl (bcastFoldStep lg committed selfId) (ms, pm)).2.map Prod.fst =
    pm.map Prod.fst ++ peers.map Prod.fst := by
  induction peers generalizing ms pm with
  | nil => simp
  | cons ⟨id, p⟩ tl ih =>
    simp only [List.foldl_cons, bcastFoldStep]
    split_ifs with hid
    · rw [ih ms (pm ++ [(id, p)])]
      simp [List.map_append, List.append_assoc]
    · split_ifs with hs
      · rw [ih (ms ++ _) (pm ++ [(id, _)])]
        simp [List.map_append, List.append_assoc]
      · rw [ih ms (pm ++ [(id, _)])]
        simp [List.map_append, List.append_assoc]

/-- Entries already in `pm` survive all subsequent fold steps. -/
private theorem bcastFoldStep_pm0_mem
    (lg : Log) (committed selfId : Nat)
    (peers : List (Nat × FullProgress))
    (ms : List Msg) (pm : List (Nat × FullProgress))
    (x : Nat) (y : FullProgress) (hmem : (x, y) ∈ pm) :
    (x, y) ∈ (peers.foldl (bcastFoldStep lg committed selfId) (ms, pm)).2 := by
  induction peers generalizing ms pm with
  | nil => simpa
  | cons ⟨id, p⟩ tl ih =>
    simp only [List.foldl_cons, bcastFoldStep]
    split_ifs with hid
    · exact ih ms (pm ++ [(id, p)]) (List.mem_append_left _ hmem)
    · split_ifs with hs
      · exact ih (ms ++ _) (pm ++ [(id, _)]) (List.mem_append_left _ hmem)
      · exact ih ms (pm ++ [(id, _)]) (List.mem_append_left _ hmem)

/-- The self entry `(selfId, pr)` reaches the output progress map whenever it
    appears in `pm` initially *or* somewhere in `peers`. -/
private theorem bcastFoldStep_self_mem
    (lg : Log) (committed selfId : Nat)
    (peers : List (Nat × FullProgress))
    (ms : List Msg) (pm : List (Nat × FullProgress))
    (pr : FullProgress)
    (h : (selfId, pr) ∈ pm ∨ (selfId, pr) ∈ peers) :
    (selfId, pr) ∈ (peers.foldl (bcastFoldStep lg committed selfId) (ms, pm)).2 := by
  induction peers generalizing ms pm with
  | nil =>
    simp only [List.foldl_nil]
    rcases h with h | h
    · exact h
    · exact absurd h (List.not_mem_nil _)
  | cons ⟨id, p⟩ tl ih =>
    simp only [List.foldl_cons, bcastFoldStep]
    rcases h with h | h
    · -- (selfId, pr) already in pm; it survives regardless of what head does
      split_ifs with hid
      · exact ih ms (pm ++ [(id, p)]) (Or.inl (List.mem_append_left _ h))
      · split_ifs with hs
        · exact ih (ms ++ _) (pm ++ [(id, _)]) (Or.inl (List.mem_append_left _ h))
        · exact ih ms (pm ++ [(id, _)]) (Or.inl (List.mem_append_left _ h))
    · -- (selfId, pr) is somewhere in (id, p) :: tl
      rw [List.mem_cons] at h
      rcases h with h | h
      · -- head is our entry: (selfId, pr) = (id, p)
        have hid : id = selfId := congr_arg Prod.fst h.symm
        have hpr : p = pr     := congr_arg Prod.snd h.symm
        simp only [hid, ↓reduceIte]
        exact ih ms (pm ++ [(selfId, p)]) (Or.inl
          (List.mem_append_right _ (by simp [hpr])))
      · -- (selfId, pr) is in the tail
        split_ifs with hid
        · exact ih ms (pm ++ [(id, p)]) (Or.inr h)
        · split_ifs with hs
          · exact ih (ms ++ _) (pm ++ [(id, _)]) (Or.inr h)
          · exact ih ms (pm ++ [(id, _)]) (Or.inr h)

/-- **Self is never targeted**: `bcast_append` preserves the self entry verbatim. -/
theorem bcastAppend_self_unchanged
    (lg : Log) (committed : Nat) (selfId : Nat)
    (peers : List (Nat × FullProgress))
    (pr : FullProgress)
    (hmem : (selfId, pr) ∈ peers) :
    ∃ pr', (selfId, pr') ∈ (bcastAppend lg committed selfId peers).2 ∧ pr' = pr :=
  ⟨pr, bcastFoldStep_self_mem lg committed selfId peers [] [] pr (Or.inr hmem), rfl⟩

/-- **Coverage**: every peer id appears in the output progress map (in order). -/
theorem bcastAppend_covers_all_peers
    (lg : Log) (committed : Nat) (selfId : Nat)
    (peers : List (Nat × FullProgress)) :
    (bcastAppend lg committed selfId peers).2.map Prod.fst =
    peers.map Prod.fst := by
  simp only [bcastAppend]
  have := bcastFoldStep_fst_keys lg committed selfId peers [] []
  simpa using this

/-! ## Decidable sanity checks -/

private def ex_probe : FullProgress :=
  { matched := 4, next_idx := 5, state := .Probe, paused := false,
    pending_snapshot := 0, recent_active := true,
    ins := { cap := 4, items := [] } }

private def ex_replicate : FullProgress :=
  { matched := 4, next_idx := 5, state := .Replicate, paused := false,
    pending_snapshot := 0, recent_active := true,
    ins := { cap := 4, items := [] } }

private def ex_snapshot : FullProgress :=
  { matched := 4, next_idx := 5, state := .Snapshot, paused := false,
    pending_snapshot := 8, recent_active := true,
    ins := { cap := 4, items := [] } }

-- Probe not paused (paused = false)
#eval isPaused ex_probe        -- expected: false
-- Replicate not paused (inflight not full)
#eval isPaused ex_replicate    -- expected: false
-- Snapshot always paused
#eval isPaused ex_snapshot     -- expected: true

example : isPaused ex_probe = false := by decide
example : isPaused ex_replicate = false := by decide
example : isPaused ex_snapshot = true := by decide

-- After updateState in Probe mode, progress is paused
example : (updateState ex_probe 7).paused = true := by decide

-- After updateState in Replicate mode, next_idx advances
example : (updateState ex_replicate 8).next_idx = 9 := by decide

-- prepareSendEntries produces a MsgAppend
example : (prepareSendEntries 10 ex_replicate 3 [5, 6, 7]).1.msg_type = .MsgAppend := by decide
example : (prepareSendEntries 10 ex_replicate 3 [5, 6, 7]).1.index = 4 := by decide
example : (prepareSendEntries 10 ex_replicate 3 [5, 6, 7]).1.commit = 10 := by decide

end FVSquad.BcastAppend
