/-!
# HandleAppendResponse — Lean 4 Specification (Phases 3 + 4 + 5)

Models `RaftCore::handle_append_response` in `src/raft.rs` (≈ lines 1649–1863).

## Relevant Rust code (condensed)

```rust
fn handle_append_response(&mut self, m: &Message) {
    let mut next_probe_index: u64 = m.reject_hint;
    if m.reject && m.log_term > 0 {
        next_probe_index = self.raft_log.find_conflict_by_term(m.reject_hint, m.log_term).0;
    }
    let pr = match self.prs.get_mut(m.from) { Some(pr) => pr, None => return };
    pr.recent_active = true;
    pr.update_committed(m.commit);
    if m.reject {
        if pr.maybe_decr_to(m.index, next_probe_index, m.request_snapshot) {
            if pr.state == ProgressState::Replicate { pr.become_probe(); }
            self.send_append(m.from);
        }
        return;
    }
    let old_paused = pr.is_paused();
    if !pr.maybe_update(m.index) { return; }
    match pr.state {
        Probe     => pr.become_replicate(),
        Snapshot  => if pr.is_snapshot_caught_up() { pr.become_probe(); }
        Replicate => pr.ins.free_to(m.get_index()),
    }
    if self.maybe_commit() {
        if self.should_bcast_commit() { self.bcast_append() }
    } else if old_paused {
        self.send_append(m.from);
    }
    self.send_append_aggressively(m.from);
    if Some(m.from) == self.r.lead_transferee {
        let last_index = self.r.raft_log.last_index();
        let pr = self.prs.get_mut(m.from).unwrap();
        if pr.matched == last_index { self.send_timeout_now(m.from); }
    }
}
```

## Model scope and approximations

* All indices and terms are `Nat` (Rust `u64`; overflow not modelled).
* **`findConflictByTerm`** is modelled as a decreasing index loop returning the
  largest index ≤ `hint` at which the leader's log term is ≤ `term`; we use
  structural recursion on `hint` (bounded by `hint + 1` steps) for termination.
* **`Progress`** is a self-contained record mirroring the Rust struct.
* **`maybeDecrTo`** and **`maybeUpdate`** mirror the Rust logic exactly.
* **Inflights** are abstracted as a Boolean `insFull : Bool`; `free_to` just
  clears the flag.  The full sliding-window model is in `FVSquad.Inflights`.
* **`send_append` / `bcast_append` / `send_timeout_now`** are abstracted as
  Boolean outputs (`sentAppend`, `broadcastAppend`, `sentTimeoutNow`).
* **`maybe_commit` / `should_bcast_commit`** are abstract Boolean inputs.
* **Log state** is abstracted as `logTerm : Nat → Option Nat` and `lastIndex : Nat`.
* **Unknown-peer early-exit** is modelled with `Option Progress`.
* I/O, logging, and storage persistence are omitted.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace FVSquad.HandleAppendResponse

/-! ## Types -/

/-- Raft progress state for a follower peer. -/
inductive ProgressState where
  | Probe
  | Replicate
  | Snapshot
  deriving Repr, DecidableEq

open ProgressState

/-- A follower's replication progress tracked by the leader.
    We abstract `Inflights` to a single Boolean `insFull`. -/
structure Progress where
  matched              : Nat
  next_idx             : Nat
  state                : ProgressState
  paused               : Bool    -- used in Probe mode
  pending_snapshot     : Nat     -- 0 = no pending snapshot
  pending_req_snapshot : Nat     -- 0 = no pending request
  recent_active        : Bool
  insFull              : Bool    -- abstract inflight window
  committed_index      : Nat
  deriving Repr

/-- An incoming MsgAppendResponse. -/
structure AppRespMsg where
  from_           : Nat
  index           : Nat
  reject          : Bool
  reject_hint     : Nat
  log_term        : Nat     -- 0 if no term available
  commit          : Nat
  request_snapshot : Nat   -- 0 = INVALID_INDEX (no request)
  deriving Repr, DecidableEq

/-- Output of the handler (abstract effect bundle). -/
structure HandlerOutput where
  pr              : Option Progress   -- updated progress (none = unknown peer)
  sentAppend      : Bool
  broadcastAppend : Bool
  sentTimeoutNow  : Bool
  deriving Repr

/-! ## Helper: `is_paused` -/

def isPaused (p : Progress) : Bool :=
  match p.state with
  | Probe     => p.paused
  | Replicate => p.insFull
  | Snapshot  => true

/-! ## Helper: `update_committed` -/

def updateCommitted (p : Progress) (ci : Nat) : Progress :=
  { p with committed_index := max p.committed_index ci }

/-! ## Helper: `resume` / `become_probe` / `become_replicate` -/

def resume (p : Progress) : Progress := { p with paused := false }

def becomeProbe (p : Progress) : Progress :=
  let next := if p.state == Snapshot
                then max (p.matched + 1) (p.pending_snapshot + 1)
                else p.matched + 1
  { p with state := Probe, paused := false, pending_snapshot := 0, insFull := false,
           next_idx := next }

def becomeReplicate (p : Progress) : Progress :=
  { p with state := Replicate, paused := false, insFull := false,
           next_idx := p.matched + 1 }

/-! ## Helper: `is_snapshot_caught_up` -/

def isSnapshotCaughtUp (p : Progress) : Bool :=
  p.state == Snapshot && p.matched >= p.pending_snapshot

/-! ## Helper: `maybe_update` -/

/-- Returns `(updated_progress, did_update)`. -/
def maybeUpdate (p : Progress) (n : Nat) : Progress × Bool :=
  let need_update := p.matched < n
  let p' := if need_update then resume { p with matched := n } else p
  let p'' := if p'.next_idx < n + 1 then { p' with next_idx := n + 1 } else p'
  (p'', need_update)

/-! ## Helper: `maybe_decr_to` -/

/-- `INVALID_INDEX` is modelled as 0. -/
def INVALID_INDEX : Nat := 0

/-- Returns `(updated_progress, did_decrement)`. -/
def maybeDecrTo (p : Progress) (rejected match_hint req_snap : Nat) : Progress × Bool :=
  if p.state == Replicate then
    if rejected < p.matched
        || (rejected == p.matched && req_snap == INVALID_INDEX) then
      (p, false)
    else if req_snap == INVALID_INDEX then
      ({ p with next_idx := p.matched + 1 }, true)
    else
      ({ p with pending_req_snapshot := req_snap }, true)
  else
    if (p.next_idx == 0 || p.next_idx - 1 ≠ rejected) && req_snap == INVALID_INDEX then
      (p, false)
    else
      if req_snap == INVALID_INDEX then
        let new_next := min rejected (match_hint + 1)
        let new_next := max new_next (p.matched + 1)
        (resume { p with next_idx := new_next }, true)
      else if p.pending_req_snapshot == INVALID_INDEX then
        (resume { p with pending_req_snapshot := req_snap }, true)
      else
        (resume p, true)

/-! ## `findConflictByTerm` (leader-side log) -/

/-- Leader log abstraction: a partial function from index to term.
    `none` means the entry is compacted (not available). -/
abbrev LeaderLog := Nat → Option Nat

/-- Scan left from `hint` until we find an index where `logTerm idx ≤ term`.
    We use the `fuel` trick (fuel = hint + 1) for structural recursion. -/
def findConflictByTermAux (log : LeaderLog) (term : Nat) : Nat → Nat → Nat
  | 0,        idx => idx
  | fuel + 1, idx =>
    match log idx with
    | none    => idx            -- compacted: stop here
    | some t  => if t > term
                   then findConflictByTermAux log term fuel (idx - 1)
                   else idx

/-- `findConflictByTerm hint term`: returns the largest index ≤ hint
    at which the leader's log term is ≤ term. -/
def findConflictByTerm (log : LeaderLog) (hint term : Nat) : Nat :=
  findConflictByTermAux log term (hint + 1) hint

/-! ## Main handler model -/

/-- Abstract leader state needed by the handler. -/
structure LeaderState where
  log           : LeaderLog
  lastIndex     : Nat
  leadTransferee : Option Nat   -- None = no transfer in progress
  mayCommit     : Bool          -- abstract: whether maybe_commit() fires
  shouldBcast   : Bool          -- abstract: should_bcast_commit()

/-- Model of `handle_append_response`. -/
def handleAppendResponse
    (ls : LeaderState) (m : AppRespMsg) (pr_opt : Option Progress)
    : HandlerOutput :=
  -- Fast-backtrack probe index
  let next_probe_index :=
    if m.reject && m.log_term > 0
      then findConflictByTerm ls.log m.reject_hint m.log_term
      else m.reject_hint
  -- Unknown peer: early exit
  match pr_opt with
  | none => { pr := none, sentAppend := false, broadcastAppend := false,
               sentTimeoutNow := false }
  | some pr =>
    -- Mark active; update committed
    let pr := { pr with recent_active := true }
    let pr := updateCommitted pr m.commit
    if m.reject then
      -- Rejection path
      let (pr', did_decr) := maybeDecrTo pr m.index next_probe_index m.request_snapshot
      if did_decr then
        let pr' := if pr'.state == Replicate then becomeProbe pr' else pr'
        { pr := some pr', sentAppend := true, broadcastAppend := false,
          sentTimeoutNow := false }
      else
        { pr := some pr', sentAppend := false, broadcastAppend := false,
          sentTimeoutNow := false }
    else
      -- Acceptance path
      let old_paused := isPaused pr
      let (pr', did_update) := maybeUpdate pr m.index
      if !did_update then
        { pr := some pr', sentAppend := false, broadcastAppend := false,
          sentTimeoutNow := false }
      else
        -- State transition
        let pr' := match pr'.state with
          | Probe     => becomeReplicate pr'
          | Snapshot  => if isSnapshotCaughtUp pr' then becomeProbe pr' else pr'
          | Replicate => { pr' with insFull := false }  -- free_to abstracted as clear
        -- Commit / send decisions
        let bcast     := ls.mayCommit && ls.shouldBcast
        let send_app  := (!ls.mayCommit && old_paused)
                      || (ls.mayCommit && !ls.shouldBcast)   -- aggressive re-send
        -- Leadership transfer
        let sent_tnow :=
          ls.leadTransferee == some m.from_ && pr'.matched == ls.lastIndex
        { pr := some pr', sentAppend := send_app, broadcastAppend := bcast,
          sentTimeoutNow := sent_tnow }

/-! ## Properties -/

-- ─────────────────────────────────────────────────────────────────────────────
-- P1: recent_active is always set on any non-early-exit path
-- ─────────────────────────────────────────────────────────────────────────────

theorem p1_recent_active (ls : LeaderState) (m : AppRespMsg) (pr : Progress) :
    let out := handleAppendResponse ls m (some pr)
    out.pr.isSome → (out.pr.get! ).recent_active = true := by
  simp [handleAppendResponse, updateCommitted, maybeDecrTo, maybeUpdate,
        becomeProbe, becomeReplicate, isPaused]
  split_ifs <;> simp_all [Option.get!]

-- ─────────────────────────────────────────────────────────────────────────────
-- P2: committed_index is monotonically non-decreasing
-- ─────────────────────────────────────────────────────────────────────────────

theorem p2_committed_mono (p : Progress) (ci : Nat) :
    p.committed_index ≤ (updateCommitted p ci).committed_index := by
  simp [updateCommitted]
  omega

theorem p2b_committed_ge_msg (p : Progress) (ci : Nat) :
    ci ≤ (updateCommitted p ci).committed_index := by
  simp [updateCommitted]
  omega

-- ─────────────────────────────────────────────────────────────────────────────
-- P3: unknown peer ⟹ no output / no state change
-- ─────────────────────────────────────────────────────────────────────────────

theorem p3_unknown_peer (ls : LeaderState) (m : AppRespMsg) :
    let out := handleAppendResponse ls m none
    out.pr = none ∧ out.sentAppend = false ∧ out.broadcastAppend = false
      ∧ out.sentTimeoutNow = false := by
  simp [handleAppendResponse]

-- ─────────────────────────────────────────────────────────────────────────────
-- P4: findConflictByTerm returns an index ≤ hint
-- ─────────────────────────────────────────────────────────────────────────────

theorem p4_fcbt_le_hint (log : LeaderLog) (term : Nat) :
    ∀ fuel idx, idx ≤ fuel → findConflictByTermAux log term fuel idx ≤ idx := by
  intro fuel
  induction fuel with
  | zero => intro idx hle; simp [findConflictByTermAux]
  | succ n ih =>
    intro idx _
    simp only [findConflictByTermAux]
    split
    · omega
    · rename_i t ht
      split_ifs with h
      · have hlt : idx - 1 ≤ n := by omega
        have := ih (idx - 1) hlt
        omega
      · omega

theorem p4_fcbt_hint_le (log : LeaderLog) (hint term : Nat) :
    findConflictByTerm log hint term ≤ hint := by
  simp [findConflictByTerm]
  have := p4_fcbt_le_hint log term (hint + 1) hint (by omega)
  omega

-- ─────────────────────────────────────────────────────────────────────────────
-- P5: On rejection with log_term > 0, next_probe_index ≤ reject_hint
-- ─────────────────────────────────────────────────────────────────────────────

theorem p5_probe_idx_le_hint (ls : LeaderState) (m : AppRespMsg)
    (hrej : m.reject = true) (hlt : m.log_term > 0) :
    findConflictByTerm ls.log m.reject_hint m.log_term ≤ m.reject_hint := by
  exact p4_fcbt_hint_le ls.log m.reject_hint m.log_term

-- ─────────────────────────────────────────────────────────────────────────────
-- P6: maybe_update — stale message ⟹ did_update = false
-- ─────────────────────────────────────────────────────────────────────────────

theorem p6_stale_no_update (p : Progress) (n : Nat) (h : n ≤ p.matched) :
    (maybeUpdate p n).2 = false := by
  simp [maybeUpdate]
  omega

-- ─────────────────────────────────────────────────────────────────────────────
-- P7: maybe_update — fresh message ⟹ matched advances to n
-- ─────────────────────────────────────────────────────────────────────────────

theorem p7_update_advances_matched (p : Progress) (n : Nat) (h : p.matched < n) :
    (maybeUpdate p n).1.matched = n := by
  simp [maybeUpdate, resume, h]
  omega

-- ─────────────────────────────────────────────────────────────────────────────
-- P8: maybe_update — next_idx ≥ n + 1 after update
-- ─────────────────────────────────────────────────────────────────────────────

theorem p8_update_next_idx (p : Progress) (n : Nat) :
    let p' := (maybeUpdate p n).1
    p'.next_idx ≥ n + 1 := by
  simp only [maybeUpdate, resume]
  split_ifs <;> omega

-- ─────────────────────────────────────────────────────────────────────────────
-- P9: Probe → Replicate state transition on success
-- ─────────────────────────────────────────────────────────────────────────────

theorem p9_probe_becomes_replicate (p : Progress) (h : p.state = Probe) :
    (becomeReplicate p).state = Replicate := by
  simp [becomeReplicate]

-- ─────────────────────────────────────────────────────────────────────────────
-- P10: Snapshot → Probe iff snapshot caught up
-- ─────────────────────────────────────────────────────────────────────────────

theorem p10_snapshot_probe_iff (p : Progress) (hs : p.state = Snapshot) :
    (if isSnapshotCaughtUp p then becomeProbe p else p).state = Probe
    ↔ p.matched ≥ p.pending_snapshot := by
  simp [isSnapshotCaughtUp, becomeProbe, hs]
  split_ifs with h
  · simp
  · push_neg at h
    constructor
    · intro heq; simp [hs] at heq
    · intro hge; exact absurd hge h

-- ─────────────────────────────────────────────────────────────────────────────
-- P11: becomeReplicate — next_idx = matched + 1
-- ─────────────────────────────────────────────────────────────────────────────

theorem p11_replicate_next_idx (p : Progress) :
    (becomeReplicate p).next_idx = p.matched + 1 := by
  simp [becomeReplicate]

-- ─────────────────────────────────────────────────────────────────────────────
-- P12: maybeDecrTo — Replicate stale (rejected < matched) ⟹ false
-- ─────────────────────────────────────────────────────────────────────────────

theorem p12_decr_stale_replicate (p : Progress) (rej hint req : Nat)
    (hstate : p.state = Replicate) (hstale : rej < p.matched) :
    (maybeDecrTo p rej hint req).2 = false := by
  simp [maybeDecrTo, hstate]
  omega

-- ─────────────────────────────────────────────────────────────────────────────
-- P13: maybeDecrTo — Probe, stale probe (next - 1 ≠ rejected, no snap) ⟹ false
-- ─────────────────────────────────────────────────────────────────────────────

theorem p13_decr_stale_probe (p : Progress) (rej hint : Nat)
    (hstate : p.state = Probe) (hne : p.next_idx - 1 ≠ rej) (hnz : p.next_idx ≠ 0) :
    (maybeDecrTo p rej hint INVALID_INDEX).2 = false := by
  simp [maybeDecrTo, hstate, INVALID_INDEX]
  omega

-- ─────────────────────────────────────────────────────────────────────────────
-- P14: maybeDecrTo — next_idx bounded below by matched + 1 (non-snap path)
-- ─────────────────────────────────────────────────────────────────────────────

theorem p14_decr_next_idx_floor (p : Progress) (rej hint : Nat)
    (hstate : p.state ≠ Replicate) :
    let (p', did) := maybeDecrTo p rej hint INVALID_INDEX
    did → p'.next_idx ≥ p.matched + 1 := by
  simp only [maybeDecrTo, INVALID_INDEX]
  cases hst : p.state <;> simp_all [ProgressState.decEq]
  · -- Probe
    split_ifs with h1 h2
    all_goals simp_all
    omega
  · -- Snapshot (same logic as Probe branch in maybeDecrTo)
    split_ifs with h1 h2
    all_goals simp_all
    omega

-- ─────────────────────────────────────────────────────────────────────────────
-- P15: Leadership transfer — timeout sent iff from == transferee ∧ matched == last
-- ─────────────────────────────────────────────────────────────────────────────

theorem p15_transfer_condition (ls : LeaderState) (m : AppRespMsg) (pr : Progress)
    (hrej : m.reject = false) (hupd : pr.matched < m.index) :
    let out := handleAppendResponse ls m (some pr)
    out.sentTimeoutNow = (ls.leadTransferee == some m.from_
                          && (maybeUpdate pr m.index).1.matched == ls.lastIndex
                          && (maybeUpdate pr m.index).2) := by
  simp only [handleAppendResponse, hrej, updateCommitted, maybeDecrTo, isPaused,
             becomeProbe, becomeReplicate, isSnapshotCaughtUp]
  simp only [maybeUpdate, resume]
  split_ifs <;> simp_all [Option.get!, decide_eq_true_eq]

end FVSquad.HandleAppendResponse
