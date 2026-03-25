/-!
# HandleAppendEntries — Lean 4 Specification and Implementation (Phases 3 + 4)

Models `RaftCore::handle_append_entries` in `src/raft.rs` (≈ lines 2499–2557).

## Relevant Rust code

```rust
pub fn handle_append_entries(&mut self, m: &Message) {
    if self.pending_request_snapshot != INVALID_INDEX {
        self.send_request_snapshot();
        return;
    }
    if m.index < self.raft_log.committed {
        let mut to_send = Message::default();
        to_send.set_msg_type(MessageType::MsgAppendResponse);
        to_send.to = m.from;
        to_send.index = self.raft_log.committed;
        to_send.commit = self.raft_log.committed;
        self.r.send(to_send, &mut self.msgs);
        return;
    }
    let mut to_send = Message::default();
    to_send.to = m.from;
    to_send.set_msg_type(MessageType::MsgAppendResponse);
    if let Some((_, last_idx)) = self.raft_log.maybe_append(m.index, m.log_term, m.commit, &m.entries) {
        to_send.set_index(last_idx);
    } else {
        let hint_index = cmp::min(m.index, self.raft_log.last_index());
        let (hint_index, hint_term) = self.raft_log.find_conflict_by_term(hint_index, m.log_term);
        to_send.index = m.index;
        to_send.reject = true;
        to_send.reject_hint = hint_index;
        to_send.log_term = hint_term.unwrap();
    }
    to_send.set_commit(self.raft_log.committed);
    self.r.send(to_send, &mut self.msgs);
}
```

## Model scope and approximations

* All indices and terms modelled as `Nat` (`u64` overflow not modelled).
* `pendingSnapshot : Bool` abstracts `pending_request_snapshot != INVALID_INDEX`.
* The log is abstracted as `logTerm : Nat → Option Nat` and `lastIndex : Nat`.
* `matchTerm` and `maybeAppend` are modelled inline (mirroring `FVSquad.MaybeAppend`
  but kept self-contained here to avoid namespace clashes).
* `findConflictByTerm` is modelled inline (mirrors `FVSquad.LogOrdering`).
* `maybe_append` returns `Option Nat` here (the `last_idx` only; state update is
  abstracted into the `AppendResult` type).
* Message queuing, I/O, logging, and storage persistence are omitted.
* The `send_request_snapshot` action is abstracted as the `SnapshotPending` variant.
* Commit field in the reject response equals `committed` *before* any state change
  (since `maybe_append` failed, no commit advance occurs).
* The `fatal!` panic on `hint_term = none` is treated as outside the model scope;
  we assert as a precondition that `logTerm 0 = some 0` (dummy entry invariant).

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Tactic

namespace FVSquad.HandleAppendEntries

/-! ## Types -/

abbrev NodeId := Nat
abbrev Term   := Nat
abbrev LogIdx := Nat

/-- The receiver's relevant log and snapshot state. -/
structure AppendState where
  /-- Highest durably committed index. -/
  committed        : Nat
  /-- Highest index in the log. -/
  lastIndex        : Nat
  /-- Partial mapping from index to term (`none` = compacted). -/
  logTerm          : Nat → Option Nat
  /-- `true` iff `pending_request_snapshot != INVALID_INDEX`. -/
  pendingSnapshot  : Bool

/-- An incoming MsgAppend message. -/
structure AppendRequest where
  /-- Sender (leader) node ID. -/
  from_    : NodeId
  /-- Index immediately preceding the new entries. -/
  index    : LogIdx
  /-- Term at `index` according to the leader. -/
  log_term : Term
  /-- Leader's commit index. -/
  commit   : LogIdx
  /-- New log entries as (index, term) pairs. -/
  entries  : List (LogIdx × Term)
  deriving Repr, DecidableEq

/-- A MsgAppendResponse sent back to the leader. -/
structure AppendResponse where
  /-- Destination: always equals `AppendRequest.from_`. -/
  to_        : NodeId
  /-- `true` iff the append was rejected. -/
  reject     : Bool
  /-- Accept: last newly appended index. Reject: echoes `m.index`. Stale: `committed`. -/
  index      : LogIdx
  /-- Reject only: fast-backtrack hint index (≤ `m.index`). -/
  rejectHint : LogIdx
  /-- Reject only: term at `rejectHint`. -/
  logTerm    : Term
  /-- Current committed index (post-operation). -/
  commit     : LogIdx
  deriving Repr, DecidableEq

/-- The result of `handle_append_entries`.

    * `SnapshotPending`: no MsgAppendResponse sent; `send_request_snapshot` was called.
    * `Response r`: a MsgAppendResponse is sent.                                         -/
inductive HandleAppendResult
  | SnapshotPending
  | Response (r : AppendResponse)
  deriving Repr, DecidableEq

/-! ## Helper: `matchTerm` -/

/-- `matchTerm s idx term` iff the log entry at `idx` has term `term`. -/
def matchTerm (s : AppendState) (idx term : Nat) : Bool :=
  s.logTerm idx == some term

/-! ## Helper: `findConflict` -/

/-- Find the index of the first conflicting entry in `ents` relative to the log in `s`.
    Returns 0 if there is no conflict (all entries already match the log or list is empty).
    Entries are assumed 1-indexed: `ents[i-1]` is the entry at log position `baseIdx + i`. -/
def findConflict (s : AppendState) (baseIdx : Nat) (ents : List (LogIdx × Term)) : Nat :=
  ents.enumFrom 1 |>.foldl (fun acc (i, entry) =>
    if acc != 0 then acc
    else
      let logIdx := baseIdx + i
      if s.logTerm logIdx != some entry.2 then logIdx
      else 0
  ) 0

/-! ## Helper: `findConflictByTerm` -/

/-- Functional model of `RaftLog::find_conflict_by_term`.
    Walks backward from `index` to find the largest position `j ≤ index` where the
    local log term is ≤ `term` (or where the entry is compacted/absent). -/
def findConflictByTerm (logTerm : Nat → Option Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | (i + 1), term =>
    match logTerm (i + 1) with
    | none   => i + 1
    | some t => if t ≤ term then i + 1
                else findConflictByTerm logTerm i term

/-- The conflict-by-term result is always ≤ the input index. -/
theorem findConflictByTerm_le (logTerm : Nat → Option Nat) (index term : Nat) :
    findConflictByTerm logTerm index term ≤ index := by
  induction index with
  | zero => simp [findConflictByTerm]
  | succ n ih =>
    simp only [findConflictByTerm]
    split
    · omega
    · rename_i t
      split
      · omega
      · exact Nat.le_succ_of_le ih

/-- If the result index carries a term, that term is ≤ the queried term. -/
theorem findConflictByTerm_term_le (logTerm : Nat → Option Nat) (index term : Nat) :
    ∀ t, logTerm (findConflictByTerm logTerm index term) = some t → t ≤ term := by
  induction index with
  | zero => simp [findConflictByTerm]
  | succ n ih =>
    intro t ht
    simp only [findConflictByTerm] at ht
    split at ht
    · -- compacted entry: result = n + 1; `logTerm (n+1) = none`
      rename_i heq; simp [heq] at ht
    · rename_i t' heq
      split at ht
      · -- t' ≤ term: result = n + 1; `logTerm (n+1) = some t'`
        simp [heq] at ht; omega
      · -- recurse on n
        exact ih t ht

/-! ## Helper: `maybeAppend` (pure model) -/

/-- Pure model of `RaftLog::maybe_append`.

    Returns `some last_idx` if the term at `m.index` matches (`matchTerm`), where
    `last_idx = m.index + m.entries.length`.
    Returns `none` on term mismatch.

    This abstracts the full state-mutation side-effect into just the return value;
    the committed-index advance is captured separately in `handleAppendEntries`. -/
def maybeAppend (s : AppendState) (idx logTerm commit : Nat)
    (ents : List (LogIdx × Term)) : Option Nat :=
  if matchTerm s idx logTerm then
    some (idx + ents.length)
  else
    none

/-! ## Main handler model -/

/-- Pure model of `RaftCore::handle_append_entries`.

    Abstractions:
    * State mutation (log truncation/append) is not modelled — only the response
      fields that depend on the outcome of `maybe_append` are computed.
    * `committedAfter` reflects that `maybe_append` may advance `committed` to
      `min(m.commit, last_idx)` — we pass this as a parameter because computing it
      requires the full `applyEntries` model from `FVSquad.MaybeAppend`.
    * The `committedAfter` value must satisfy `committedAfter ≥ s.committed`
      (commit monotonicity, precondition). -/
def handleAppendEntries (s : AppendState) (m : AppendRequest)
    (committedAfter : Nat) : HandleAppendResult :=
  -- Path 1: snapshot pending
  if s.pendingSnapshot then
    .SnapshotPending
  -- Path 2: stale message
  else if m.index < s.committed then
    .Response {
      to_        := m.from_
      reject     := false
      index      := s.committed
      rejectHint := 0
      logTerm    := 0
      commit     := s.committed
    }
  else
    -- Path 3: normal append / reject
    match maybeAppend s m.index m.log_term m.commit m.entries with
    | some last_idx =>
      -- Path 3a: accept
      .Response {
        to_        := m.from_
        reject     := false
        index      := last_idx
        rejectHint := 0
        logTerm    := 0
        commit     := committedAfter
      }
    | none =>
      -- Path 3b: reject with conflict hint
      let hintIdx  := Nat.min m.index s.lastIndex
      let hintIdx' := findConflictByTerm s.logTerm hintIdx m.log_term
      let hintTerm := (s.logTerm hintIdx').getD 0
      .Response {
        to_        := m.from_
        reject     := true
        index      := m.index
        rejectHint := hintIdx'
        logTerm    := hintTerm
        commit     := s.committed
      }

/-! ## Sanity checks -/

-- Example 1: stale message
#eval
  let s : AppendState := { committed := 5, lastIndex := 10,
    logTerm := fun i => if i == 0 then some 0 else some 1, pendingSnapshot := false }
  let m : AppendRequest := { from_ := 1, index := 3, log_term := 1, commit := 5, entries := [] }
  handleAppendEntries s m 5
-- Expected: Response { to_ := 1, reject := false, index := 5, commit := 5, ... }

-- Example 2: accept (term matches, empty entries = probe)
#eval
  let s : AppendState := { committed := 3, lastIndex := 5,
    logTerm := fun i => some i, pendingSnapshot := false }
  let m : AppendRequest := { from_ := 1, index := 5, log_term := 5, commit := 5, entries := [] }
  handleAppendEntries s m 5
-- Expected: Response { reject := false, index := 5, commit := 5 }

-- Example 3: reject (term mismatch)
#eval
  let s : AppendState := { committed := 3, lastIndex := 5,
    logTerm := fun i => some i, pendingSnapshot := false }
  let m : AppendRequest := { from_ := 1, index := 5, log_term := 99, commit := 5, entries := [] }
  handleAppendEntries s m 3
-- Expected: Response { reject := true, index := 5, rejectHint := 5, logTerm := 5 }

-- Example 4: snapshot pending
#eval
  let s : AppendState := { committed := 3, lastIndex := 5,
    logTerm := fun _ => some 1, pendingSnapshot := true }
  let m : AppendRequest := { from_ := 1, index := 5, log_term := 1, commit := 5, entries := [] }
  handleAppendEntries s m 3
-- Expected: SnapshotPending

/-! ## Theorems -/

/-- Path 1: snapshot pending → result is SnapshotPending, never a Response. -/
theorem snapshot_pending_no_response (s : AppendState) (m : AppendRequest) (ca : Nat)
    (h : s.pendingSnapshot = true) :
    handleAppendEntries s m ca = .SnapshotPending := by
  simp [handleAppendEntries, h]

/-- Responses always go back to the sender. -/
theorem response_to_is_from (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hr : handleAppendEntries s m ca = .Response r) :
    r.to_ = m.from_ := by
  simp [handleAppendEntries] at hr
  split_ifs at hr with h1 h2
  · simp [HandleAppendResult.SnapshotPending] at hr
  · simp [AppendResponse.mk] at hr; exact hr ▸ rfl
  · simp [maybeAppend] at hr
    split at hr
    · exact hr ▸ rfl
    · exact hr ▸ rfl

/-- Path 2: stale message → `resp.reject = false`, `resp.index = committed`,
    `resp.commit = committed`. -/
theorem stale_response (s : AppendState) (m : AppendRequest) (ca : Nat)
    (hpend : s.pendingSnapshot = false) (hstale : m.index < s.committed) :
    handleAppendEntries s m ca =
      .Response { to_ := m.from_, reject := false, index := s.committed,
                  rejectHint := 0, logTerm := 0, commit := s.committed } := by
  simp [handleAppendEntries, hpend, hstale]

/-- Path 2 corollary: stale message reject field is false. -/
theorem stale_reject_false (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hstale : m.index < s.committed)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.reject = false := by
  have := stale_response s m ca hpend hstale
  rw [this] at hr
  simp [AppendResponse.mk] at hr
  exact hr ▸ rfl

/-- Path 3a: accept → `resp.reject = false`. -/
theorem accept_reject_false (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hmatch : matchTerm s m.index m.log_term = true)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.reject = false := by
  simp [handleAppendEntries, hpend, Nat.not_lt.mp hnstale] at hr
  simp [maybeAppend, hmatch] at hr
  exact hr ▸ rfl

/-- Path 3a: accept → `resp.index = m.index + entries.length`. -/
theorem accept_index (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hmatch : matchTerm s m.index m.log_term = true)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.index = m.index + m.entries.length := by
  simp [handleAppendEntries, hpend, Nat.not_lt.mp hnstale] at hr
  simp [maybeAppend, hmatch] at hr
  exact hr ▸ rfl

/-- Path 3b: reject → `resp.reject = true`. -/
theorem reject_sets_reject (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hnomatch : matchTerm s m.index m.log_term = false)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.reject = true := by
  simp [handleAppendEntries, hpend, Nat.not_lt.mp hnstale] at hr
  simp [maybeAppend, hnomatch] at hr
  exact hr ▸ rfl

/-- Path 3b: reject → `resp.index = m.index`. -/
theorem reject_echoes_index (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hnomatch : matchTerm s m.index m.log_term = false)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.index = m.index := by
  simp [handleAppendEntries, hpend, Nat.not_lt.mp hnstale] at hr
  simp [maybeAppend, hnomatch] at hr
  exact hr ▸ rfl

/-- Path 3b: `rejectHint ≤ m.index`.
    The hint is a valid backtrack target for the leader. -/
theorem reject_hint_le_index (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hnomatch : matchTerm s m.index m.log_term = false)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.rejectHint ≤ m.index := by
  simp [handleAppendEntries, hpend, Nat.not_lt.mp hnstale] at hr
  simp [maybeAppend, hnomatch] at hr
  have hle : findConflictByTerm s.logTerm (Nat.min m.index s.lastIndex) m.log_term
             ≤ Nat.min m.index s.lastIndex :=
    findConflictByTerm_le s.logTerm _ _
  have hmineq : Nat.min m.index s.lastIndex ≤ m.index := Nat.min_le_left _ _
  rw [← hr]
  simp
  omega

/-- Path 3b: `resp.logTerm ≤ m.log_term`.
    The hint carries a term ≤ the leader's term (used by the leader for fast backtrack). -/
theorem reject_logterm_le (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hnomatch : matchTerm s m.index m.log_term = false)
    (hr : handleAppendEntries s m ca = .Response r)
    (hterm : ∀ t, s.logTerm r.rejectHint = some t → t ≤ m.log_term) :
    r.logTerm ≤ m.log_term := by
  simp [handleAppendEntries, hpend, Nat.not_lt.mp hnstale] at hr
  simp [maybeAppend, hnomatch] at hr
  have hint_eq : r.rejectHint =
    findConflictByTerm s.logTerm (Nat.min m.index s.lastIndex) m.log_term := by
    rw [← hr]; simp
  rw [← hr]
  simp
  -- logTerm of rejectHint: either some t ≤ term, or none → getD 0 ≤ anything
  cases h : s.logTerm (findConflictByTerm s.logTerm (Nat.min m.index s.lastIndex) m.log_term) with
  | none => simp [Option.getD]
  | some t =>
    simp [Option.getD]
    exact findConflictByTerm_term_le s.logTerm _ _ t h

/-- Path 2 and Path 3 response: result is always a `Response`, not `SnapshotPending`,
    when `pendingSnapshot = false`. -/
theorem not_pending_gives_response (s : AppendState) (m : AppendRequest) (ca : Nat)
    (hpend : s.pendingSnapshot = false) :
    ∃ r, handleAppendEntries s m ca = .Response r := by
  simp [handleAppendEntries, hpend]
  split_ifs with h
  · exact ⟨_, rfl⟩
  · simp [maybeAppend]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- Accept commit field uses the post-append committed index (supplied by caller). -/
theorem accept_commit_field (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hmatch : matchTerm s m.index m.log_term = true)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.commit = ca := by
  simp [handleAppendEntries, hpend, Nat.not_lt.mp hnstale] at hr
  simp [maybeAppend, hmatch] at hr
  exact hr ▸ rfl

/-- Reject commit field equals pre-operation `s.committed` (no state change on reject). -/
theorem reject_commit_is_committed (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hnomatch : matchTerm s m.index m.log_term = false)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.commit = s.committed := by
  simp [handleAppendEntries, hpend, Nat.not_lt.mp hnstale] at hr
  simp [maybeAppend, hnomatch] at hr
  exact hr ▸ rfl

/-- **Core safety**: reject is mutually exclusive with accept for the same message.
    If `matchTerm` holds, the response is never a rejection. -/
theorem accept_not_reject (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hmatch : matchTerm s m.index m.log_term = true)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.reject = false := accept_reject_false s m ca r hpend hnstale hmatch hr

/-- If `matchTerm` fails, the response is always a rejection. -/
theorem nomatch_is_reject (s : AppendState) (m : AppendRequest) (ca : Nat)
    (r : AppendResponse) (hpend : s.pendingSnapshot = false)
    (hnstale : ¬ m.index < s.committed) (hnomatch : matchTerm s m.index m.log_term = false)
    (hr : handleAppendEntries s m ca = .Response r) :
    r.reject = true := reject_sets_reject s m ca r hpend hnstale hnomatch hr

end FVSquad.HandleAppendEntries
