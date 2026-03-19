/-!
# ReadOnly — Lean 4 Specification and Implementation Model

Formal specification of the `ReadOnly` struct from `raft-rs` (`src/read_only.rs`).
`ReadOnly` implements the server-side of the Raft ReadIndex protocol: it tracks
in-flight read-only requests, collects heartbeat acknowledgements, and serves
requests in FIFO order once a quorum is reached.

## Model scope and approximations

* **Context keys**: `Vec<u8>` keys abstracted to `Nat` identifiers.
* **Peer IDs**: `u64` → `Nat`.
* **Commit index**: `u64` → `Nat` (no overflow).
* **Message payload** (`req : Message`): omitted; only the context key, commit index,
  and ack set are modelled.
* **`ReadOnlyOption`** (Safe vs LeaseBased): omitted — both modes use the same queue.
* **`pending_read_index` HashMap + `read_index_queue` VecDeque**: unified as a single
  `ReadOnlyState` carrying `queue : List Nat` (FIFO order, no dups) plus `acks` and
  `idx` functions indexed by ctx key.
* **`self_id`**: The leader's own ID, passed to `add_request` to seed the ack set.
* **Omitted**: I/O, logging, `fatal!` panic semantics, `u64` overflow,
  `ReadOnlyOption` lease logic.

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace FVSquad.ReadOnly

/-! ## State Model -/

/-- Abstract model of `ReadOnly`.

    * `queue`  — ordered list of pending ctx keys (FIFO, no duplicates).
                 Mirrors `read_index_queue`.
    * `acks`   — acknowledgement sets indexed by ctx key.
                 Mirrors `ReadIndexStatus.acks` in `pending_read_index`.
    * `idx`    — commit index recorded when each request was added.
                 Mirrors `ReadIndexStatus.index` in `pending_read_index`. -/
structure ReadOnlyState where
  queue : List Nat
  acks  : Nat → Finset Nat
  idx   : Nat → Nat

/-- **INV-2 (no-dup)**: the queue contains no duplicate ctx keys. -/
def ReadOnlyState.WF (s : ReadOnlyState) : Prop :=
  s.queue.Nodup

/-! ## Initial state -/

def emptyState : ReadOnlyState where
  queue := []
  acks  := fun _ => ∅
  idx   := fun _ => 0

theorem emptyState_wf : emptyState.WF :=
  List.nodup_nil

/-! ## `add_request` -/

/-- Model of `ReadOnly::add_request`.

    If `ctx` is already in the queue, returns the state unchanged (idempotent).
    Otherwise, appends `ctx` to the queue and seeds the ack set with `selfId`. -/
def addRequest (s : ReadOnlyState) (ctx ci selfId : Nat) : ReadOnlyState :=
  if ctx ∈ s.queue then s
  else
    { queue := s.queue ++ [ctx]
      acks  := fun c => if c = ctx then {selfId} else s.acks c
      idx   := fun c => if c = ctx then ci    else s.idx  c }

/-- **PROP-1**: addRequest is idempotent when ctx is already pending. -/
theorem addRequest_idempotent (s : ReadOnlyState) (ctx ci self : Nat)
    (hmem : ctx ∈ s.queue) :
    addRequest s ctx ci self = s := by
  simp [addRequest, hmem]

/-- **PROP-2**: addRequest preserves WF (Nodup). -/
theorem addRequest_wf (s : ReadOnlyState) (ctx ci self : Nat)
    (hwf : s.WF) :
    (addRequest s ctx ci self).WF := by
  simp only [addRequest, ReadOnlyState.WF]
  split_ifs with h
  · exact hwf
  · exact List.Nodup.append hwf (List.nodup_singleton ctx)
      (by simp [List.Disjoint]; exact h)

/-- **PROP-3**: addRequest appends ctx to the queue when it is new. -/
theorem addRequest_queue_append (s : ReadOnlyState) (ctx ci self : Nat)
    (h : ctx ∉ s.queue) :
    (addRequest s ctx ci self).queue = s.queue ++ [ctx] := by
  simp [addRequest, h]

/-- **PROP-4**: After addRequest (new ctx), ctx ∈ queue. -/
theorem addRequest_mem_queue (s : ReadOnlyState) (ctx ci self : Nat)
    (h : ctx ∉ s.queue) :
    ctx ∈ (addRequest s ctx ci self).queue := by
  simp [addRequest, h]

/-- **PROP-5**: After addRequest (new ctx), selfId ∈ acks(ctx). -/
theorem addRequest_selfId_in_acks (s : ReadOnlyState) (ctx ci self : Nat)
    (h : ctx ∉ s.queue) :
    self ∈ (addRequest s ctx ci self).acks ctx := by
  simp [addRequest, h]

/-- **PROP-6**: addRequest records the commit index for the new ctx. -/
theorem addRequest_idx (s : ReadOnlyState) (ctx ci self : Nat)
    (h : ctx ∉ s.queue) :
    (addRequest s ctx ci self).idx ctx = ci := by
  simp [addRequest, h]

/-- **PROP-7**: addRequest does not affect acks for other ctx keys. -/
theorem addRequest_acks_other (s : ReadOnlyState) (ctx ctx' ci self : Nat)
    (h : ctx ∉ s.queue) (hne : ctx' ≠ ctx) :
    (addRequest s ctx ci self).acks ctx' = s.acks ctx' := by
  simp [addRequest, h, Ne.symm hne]

/-- **PROP-8**: addRequest increments queue length by 1 for new ctx. -/
theorem addRequest_length_succ (s : ReadOnlyState) (ctx ci self : Nat)
    (h : ctx ∉ s.queue) :
    (addRequest s ctx ci self).queue.length = s.queue.length + 1 := by
  simp [addRequest, h]

/-! ## `recv_ack` -/

/-- Model of `ReadOnly::recv_ack`.

    If `ctx` is pending, inserts `id` into its ack set and returns `some newAcks`.
    Otherwise, state is unchanged and returns `none`. -/
def recvAck (s : ReadOnlyState) (id ctx : Nat) :
    ReadOnlyState × Option (Finset Nat) :=
  if ctx ∈ s.queue then
    let newAcks := s.acks ctx ∪ {id}
    ( { s with acks := fun c => if c = ctx then newAcks else s.acks c }
    , some newAcks )
  else
    (s, none)

/-- **PROP-9**: recv_ack returns Some when ctx is pending. -/
theorem recvAck_pending_some (s : ReadOnlyState) (id ctx : Nat)
    (hmem : ctx ∈ s.queue) :
    (recvAck s id ctx).2 = some (s.acks ctx ∪ {id}) := by
  simp [recvAck, hmem]

/-- **PROP-10**: recv_ack inserts id into the ack set for ctx. -/
theorem recvAck_id_in_acks (s : ReadOnlyState) (id ctx : Nat)
    (hmem : ctx ∈ s.queue) :
    id ∈ (recvAck s id ctx).1.acks ctx := by
  simp [recvAck, hmem, Finset.mem_union, Finset.mem_singleton]

/-- **PROP-11**: Prior acks are preserved after recv_ack. -/
theorem recvAck_prior_acks (s : ReadOnlyState) (id ctx : Nat)
    (hmem : ctx ∈ s.queue) (x : Nat) (hx : x ∈ s.acks ctx) :
    x ∈ (recvAck s id ctx).1.acks ctx := by
  simp [recvAck, hmem, Finset.mem_union]
  exact Or.inl hx

/-- **PROP-12**: recv_ack for unknown ctx leaves state unchanged. -/
theorem recvAck_not_pending (s : ReadOnlyState) (id ctx : Nat)
    (h : ctx ∉ s.queue) :
    recvAck s id ctx = (s, none) := by
  simp [recvAck, h]

/-- **PROP-13**: recv_ack preserves WF. -/
theorem recvAck_wf (s : ReadOnlyState) (id ctx : Nat)
    (hwf : s.WF) : (recvAck s id ctx).1.WF := by
  simp only [recvAck, ReadOnlyState.WF]
  split_ifs with h <;> exact hwf

/-- **PROP-14**: recv_ack does not change the queue. -/
theorem recvAck_queue_unchanged (s : ReadOnlyState) (id ctx : Nat) :
    (recvAck s id ctx).1.queue = s.queue := by
  simp [recvAck]
  split_ifs <;> simp

/-! ## `advance` -/

/-- **Auxiliary lemma**: `a` is a member of `l.take (l.indexOf a + 1)` whenever `a ∈ l`.
    Proof is by structural induction on `l`: at the head the element is found immediately;
    otherwise indexOf recurses and take peels off one more cons cell. -/
private lemma mem_take_indexOf (l : List Nat) (a : Nat) (h : a ∈ l) :
    a ∈ l.take (l.indexOf a + 1) := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.mem_cons] at h
    by_cases heq : hd = a
    · -- head matches: indexOf = 0, take 1 = [hd = a]
      subst heq; simp
    · -- head differs: a ∈ tl, indexOf (hd::tl) a = indexOf tl a + 1
      have hmem : a ∈ tl := h.resolve_left (fun e => heq e.symm)
      have hind : (hd :: tl).indexOf a = tl.indexOf a + 1 := by
        simp [List.indexOf_cons, show hd ≠ a from heq]
      rw [hind]
      -- (hd::tl).take (tl.indexOf a + 1 + 1)  =  hd :: tl.take (tl.indexOf a + 1)
      -- by the definition of List.take (third clause: take (n+1) (a::l) = a :: take n l)
      show a ∈ hd :: tl.take (tl.indexOf a + 1)
      exact List.mem_cons_of_mem hd (ih hmem)

/-- Helper: find the 0-based position of `ctx` in `queue`, or `queue.length` if absent.
    Wraps `List.indexOf` which has this exact semantics in Lean 4. -/
abbrev findPos (queue : List Nat) (ctx : Nat) : Nat := queue.indexOf ctx

/-- Model of `ReadOnly::advance`.

    Finds the position of `ctx` in the queue.
    * If found at position `i` (0-indexed): removes queue entries `0..=i`
      (the prefix ending at ctx), clears their acks/idx data, and returns the prefix
      as the list of completed ctx keys.
    * If not found: returns the state unchanged and an empty list. -/
def advance (s : ReadOnlyState) (ctx : Nat) : ReadOnlyState × List Nat :=
  let i := findPos s.queue ctx
  if i < s.queue.length then
    let prefix := s.queue.take (i + 1)
    let rest   := s.queue.drop  (i + 1)
    ( { s with
        queue := rest
        acks  := fun c => if c ∈ prefix then ∅ else s.acks c
        idx   := fun c => if c ∈ prefix then 0  else s.idx  c }
    , prefix )
  else
    (s, [])

/-- **PROP-15**: advance is a no-op when ctx is not in the queue.
    (Relies on `List.indexOf_eq_length` or equivalent for ctx ∉ queue.) -/
theorem advance_not_in_queue (s : ReadOnlyState) (ctx : Nat)
    (h : ctx ∉ s.queue) :
    advance s ctx = (s, []) := by
  simp only [advance, findPos]
  have hlen : s.queue.indexOf ctx = s.queue.length :=
    List.indexOf_eq_length.mpr h
  rw [hlen]
  simp [Nat.lt_irrefl]

/-- **PROP-16**: advance preserves WF (drop of Nodup list is Nodup). -/
theorem advance_wf (s : ReadOnlyState) (ctx : Nat)
    (hwf : s.WF) : (advance s ctx).1.WF := by
  simp only [advance, findPos, ReadOnlyState.WF]
  split_ifs with h
  · -- advance does something: queue becomes drop (indexOf ctx + 1)
    exact hwf.drop _
  · -- advance is a no-op: queue unchanged
    exact hwf

/-- **PROP-17**: The returned prefix and the remaining queue reconstruct the original queue. -/
theorem advance_splits_queue (s : ReadOnlyState) (ctx : Nat) :
    (advance s ctx).2 ++ (advance s ctx).1.queue = s.queue := by
  simp only [advance, findPos]
  split_ifs with h
  · -- true branch: prefix ++ rest = s.queue
    simp only
    exact List.take_append_drop _ s.queue
  · -- false branch: [] ++ s.queue = s.queue
    simp

/-- **PROP-18**: When ctx is in the queue, advance returns queue.take (indexOf ctx + 1). -/
theorem advance_returns_prefix (s : ReadOnlyState) (ctx : Nat)
    (hmem : ctx ∈ s.queue) :
    (advance s ctx).2 = s.queue.take (s.queue.indexOf ctx + 1) := by
  simp only [advance, findPos]
  have hlt : s.queue.indexOf ctx < s.queue.length :=
    List.indexOf_lt_length.mpr hmem
  simp [hlt]

/-- **PROP-19**: When ctx is in the queue, it appears in the returned prefix. -/
theorem advance_ctx_in_prefix (s : ReadOnlyState) (ctx : Nat)
    (hmem : ctx ∈ s.queue) :
    ctx ∈ (advance s ctx).2 := by
  rw [advance_returns_prefix s ctx hmem]
  exact mem_take_indexOf s.queue ctx hmem

/-- **PROP-20**: After advance, ctx is no longer in the remaining queue.
    Key steps: queue.Nodup implies ctx appears exactly once;
    count split via take_append_drop shows the drop (i+1) portion has count 0. -/
theorem advance_removes_ctx (s : ReadOnlyState) (ctx : Nat)
    (hmem : ctx ∈ s.queue) (hwf : s.WF) :
    ctx ∉ (advance s ctx).1.queue := by
  simp only [advance, findPos, ReadOnlyState.WF] at *
  have hlt : s.queue.indexOf ctx < s.queue.length :=
    List.indexOf_lt_length.mpr hmem
  simp [hlt]
  intro hmem'
  -- Since s.queue.Nodup, ctx appears exactly once total.
  -- It is in take (i+1) (PROP-19 approach) AND in drop (i+1) (hmem'),
  -- giving count ≥ 2, contradicting Nodup.
  have hone : s.queue.count ctx ≤ 1 := hwf.count_le_one ctx
  have hdrop : 0 < (s.queue.drop (s.queue.indexOf ctx + 1)).count ctx :=
    List.count_pos_iff_mem.mpr hmem'
  have htake : 0 < (s.queue.take (s.queue.indexOf ctx + 1)).count ctx :=
    List.count_pos_iff_mem.mpr (mem_take_indexOf s.queue ctx hmem)
  have hsplit : s.queue.count ctx =
      (s.queue.take (s.queue.indexOf ctx + 1)).count ctx +
      (s.queue.drop  (s.queue.indexOf ctx + 1)).count ctx := by
    conv_lhs => rw [← List.take_append_drop (s.queue.indexOf ctx + 1) s.queue]
    rw [List.count_append]
  omega

/-- **PROP-21**: advance is idempotent (calling again for same ctx is a no-op). -/
theorem advance_idempotent (s : ReadOnlyState) (ctx : Nat)
    (hmem : ctx ∈ s.queue) (hwf : s.WF) :
    let s' := (advance s ctx).1
    advance s' ctx = (s', []) := by
  apply advance_not_in_queue
  exact advance_removes_ctx s ctx hmem hwf

/-! ## `last_pending_request_ctx` -/

/-- Model of `ReadOnly::last_pending_request_ctx`. -/
def lastPendingRequestCtx (s : ReadOnlyState) : Option Nat :=
  s.queue.getLast?

/-- **PROP-22**: Equivalent to getLast? on the queue. -/
theorem lastPendingRequestCtx_eq (s : ReadOnlyState) :
    lastPendingRequestCtx s = s.queue.getLast? := rfl

/-- **PROP-23**: Returns None iff the queue is empty. -/
theorem lastPendingRequestCtx_none_iff (s : ReadOnlyState) :
    lastPendingRequestCtx s = none ↔ s.queue = [] := by
  simp [lastPendingRequestCtx, List.getLast?_eq_none_iff]

/-- **PROP-24**: After addRequest (new ctx), lastPendingRequestCtx = some ctx. -/
theorem addRequest_lastCtx (s : ReadOnlyState) (ctx ci self : Nat)
    (h : ctx ∉ s.queue) :
    lastPendingRequestCtx (addRequest s ctx ci self) = some ctx := by
  simp only [addRequest, lastPendingRequestCtx, h, ↓reduceIte]
  simp [List.getLast?_append]

/-! ## `pending_read_count` -/

/-- Model of `ReadOnly::pending_read_count`. -/
def pendingReadCount (s : ReadOnlyState) : Nat :=
  s.queue.length

/-- **PROP-25**: pendingReadCount = queue.length (definitional). -/
theorem pendingReadCount_eq (s : ReadOnlyState) :
    pendingReadCount s = s.queue.length := rfl

/-- **PROP-26**: empty state has count 0. -/
theorem emptyState_count : pendingReadCount emptyState = 0 := by
  simp [pendingReadCount, emptyState]

/-- **PROP-27**: addRequest (new ctx) increments the count by 1. -/
theorem addRequest_count_succ (s : ReadOnlyState) (ctx ci self : Nat)
    (h : ctx ∉ s.queue) :
    pendingReadCount (addRequest s ctx ci self) = pendingReadCount s + 1 := by
  simp [pendingReadCount, addRequest, h]

/-- **PROP-28**: advance with ctx at position i reduces count by (i + 1). -/
theorem advance_count_sub (s : ReadOnlyState) (ctx : Nat)
    (hmem : ctx ∈ s.queue) :
    pendingReadCount (advance s ctx).1 + (s.queue.indexOf ctx + 1) =
    pendingReadCount s := by
  simp only [advance, findPos, pendingReadCount]
  have hlt : s.queue.indexOf ctx < s.queue.length :=
    List.indexOf_lt_length.mpr hmem
  simp [hlt, List.length_drop]
  omega

/-! ## Cross-operation properties -/

/-- **PROP-29**: recv_ack does not affect the pending count. -/
theorem recvAck_count_unchanged (s : ReadOnlyState) (id ctx : Nat) :
    pendingReadCount (recvAck s id ctx).1 = pendingReadCount s := by
  simp [pendingReadCount, recvAck_queue_unchanged]

/-- **PROP-30**: After addRequest then recv_ack from a second peer, both IDs are in acks. -/
theorem addRequest_then_recvAck (s : ReadOnlyState) (ctx ci self peer : Nat)
    (h : ctx ∉ s.queue) :
    let s1 := addRequest s ctx ci self
    let s2 := (recvAck s1 peer ctx).1
    self ∈ s2.acks ctx ∧ peer ∈ s2.acks ctx := by
  simp only [addRequest, recvAck, h, ↓reduceIte]
  simp [Finset.mem_union, Finset.mem_singleton]

end FVSquad.ReadOnly
