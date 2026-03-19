/-!
# Progress — Lean 4 Specification

Formal specification of the `Progress` replication tracker from
`src/tracker/progress.rs` and `src/tracker/state.rs`.

`Progress` is the Raft leader's per-follower view of the replication pipeline.
It is a three-state machine (`Probe`, `Replicate`, `Snapshot`) with two key
index fields: `matched` (highest acknowledged index) and `next_idx` (next to
send).

## Model scope and approximations

* **`Inflights` omitted**: The `ins` field (in-flight message tracker, a ring
  buffer) is omitted. `is_paused` in Replicate state is approximated as always
  `false`. Future runs can compose `Inflights.lean` with this model.
* **`committed_index` omitted**: Orthogonal to the core state machine.
* **`pending_request_snapshot` omitted**: Secondary path; omitted.
  `maybeDecrTo` models the simple `request_snapshot = INVALID_INDEX` case.
* **`u64` indices**: modelled as `Nat` (unbounded).
* **Logging/panics**: `update_state` panics in Snapshot state; omitted.
* **`resume()`**: sets `paused = false`; inlined.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace FVSquad.Progress

/-! ## State machine -/

/-- The three replication modes from `src/tracker/state.rs`. -/
inductive ProgressState where
  | Probe     -- probing: one message per heartbeat, then pause
  | Replicate -- fast-path: pipeline entries up to in-flight cap
  | Snapshot  -- snapshot in flight: all replication paused
  deriving DecidableEq, Repr, BEq

/-! ## Data model -/

/-- Lean model of `Progress`. Fields not relevant to the core state machine
    (`committed_index`, `pending_request_snapshot`, `ins`) are omitted. -/
structure Progress where
  matched          : Nat            -- highest confirmed log index
  next_idx         : Nat            -- next log index to send (> matched)
  state            : ProgressState
  paused           : Bool
  pending_snapshot : Nat            -- snapshot index (Snapshot state only)
  recent_active    : Bool
  deriving Repr

/-! ## Representation invariant -/

/-- **INV-1 (index ordering)**: the next index to send is always strictly
    beyond the last acknowledged index. -/
def valid (p : Progress) : Prop :=
  p.matched + 1 ≤ p.next_idx

/-! ## Helper -/

/-- Internal `reset_state`: set state, clear `paused` and `pending_snapshot`. -/
private def resetState (p : Progress) (s : ProgressState) : Progress :=
  { p with state := s, paused := false, pending_snapshot := 0 }

/-! ## Operations -/

/-- **`maybe_update(n)`**: process an acknowledgement of entries up to index
    `n`. Returns `(updated_progress, did_update)`.

    If `n > matched`, sets `matched := n` (and resumes), advances `next_idx`.
    Otherwise just advances `next_idx` if needed (stale ack). -/
def maybeUpdate (p : Progress) (n : Nat) : Progress × Bool :=
  if p.matched < n then
    ({ p with matched := n, paused := false,
              next_idx := Nat.max p.next_idx (n + 1) }, true)
  else
    ({ p with next_idx := Nat.max p.next_idx (n + 1) }, false)

/-- **`become_probe()`**: transition to Probe state. -/
def becomeProbe (p : Progress) : Progress :=
  let base := resetState p .Probe
  match p.state with
  | .Snapshot => { base with next_idx := Nat.max (p.matched + 1) (p.pending_snapshot + 1) }
  | _         => { base with next_idx := p.matched + 1 }

/-- **`become_replicate()`**: transition to Replicate state. -/
def becomeReplicate (p : Progress) : Progress :=
  { resetState p .Replicate with next_idx := p.matched + 1 }

/-- **`become_snapshot(snapshot_idx)`**: transition to Snapshot state. -/
def becomeSnapshot (p : Progress) (snapIdx : Nat) : Progress :=
  { resetState p .Snapshot with pending_snapshot := snapIdx }

/-- **`optimistic_update(n)`**: advance `next_idx` in Replicate mode without
    waiting for an ack. -/
def optimisticUpdate (p : Progress) (n : Nat) : Progress :=
  { p with next_idx := n + 1 }

/-- **`maybe_decr_to(rejected, match_hint)`**: process a log rejection.
    Simplified model: ignores the `request_snapshot` path
    (models the `request_snapshot = INVALID_INDEX` case). -/
def maybeDecrTo (p : Progress) (rejected : Nat) (matchHint : Nat) : Progress × Bool :=
  match p.state with
  | .Replicate =>
      if rejected ≤ p.matched then
        (p, false)     -- stale rejection
      else
        ({ p with next_idx := p.matched + 1 }, true)  -- roll back
  | _ =>
      -- stale if "rejected" doesn't correspond to what we last sent
      if p.next_idx = 0 ∨ p.next_idx - 1 ≠ rejected then
        (p, false)
      else
        let nextClamped := Nat.max (Nat.min rejected (matchHint + 1)) (p.matched + 1)
        ({ p with next_idx := nextClamped, paused := false }, true)

/-- **`is_paused()`**: is replication currently paused?
    Replicate state is never paused in this model (Inflights omitted). -/
def isPaused (p : Progress) : Bool :=
  match p.state with
  | .Probe     => p.paused
  | .Replicate => false   -- abstraction: ignores Inflights.full()
  | .Snapshot  => true

/-! ## Decidable sanity checks -/

private def ex1 : Progress :=
  { matched := 5, next_idx := 7, state := .Probe,
    paused := false, pending_snapshot := 0, recent_active := true }

example : valid ex1 := by decide

-- genuine advance: matched = 9, next_idx = 10
example : (maybeUpdate ex1 9).2 = true := by decide
example : (maybeUpdate ex1 9).1.matched = 9 := by decide
example : (maybeUpdate ex1 9).1.next_idx = 10 := by decide

-- partial advance: next_idx already ahead, stays at 7
example : (maybeUpdate ex1 6).1.next_idx = 7 := by decide

-- stale: no change to matched
example : (maybeUpdate ex1 5).2 = false := by decide
example : (maybeUpdate ex1 5).1.matched = 5 := by decide

-- becomeProbe from Probe: next_idx = matched+1 = 6
example : (becomeProbe ex1).state = .Probe := by decide
example : (becomeProbe ex1).next_idx = 6 := by decide

-- becomeProbe from Snapshot: must skip past the snapshot
private def exSnap : Progress :=
  { matched := 3, next_idx := 4, state := .Snapshot,
    paused := false, pending_snapshot := 10, recent_active := false }
example : (becomeProbe exSnap).next_idx = 11 := by decide   -- max(4, 11)

-- becomeReplicate
example : (becomeReplicate ex1).state = .Replicate := by decide
example : (becomeReplicate ex1).next_idx = 6 := by decide

-- Snapshot is always paused
example : isPaused (becomeSnapshot ex1 20) = true := by decide
example : isPaused (becomeProbe ex1) = false := by decide

/-! ## Theorems about `maybeUpdate` -/

/-- `maybeUpdate` returns `true` iff `n > matched`. -/
theorem maybeUpdate_returns_true_iff (p : Progress) (n : Nat) :
    (maybeUpdate p n).2 = true ↔ p.matched < n := by
  simp [maybeUpdate]

/-- After `maybeUpdate`, `matched = max(old.matched, n)`. -/
theorem maybeUpdate_matched (p : Progress) (n : Nat) :
    (maybeUpdate p n).1.matched = Nat.max p.matched n := by
  simp only [maybeUpdate]
  split <;> omega

/-- After `maybeUpdate`, `next_idx = max(old.next_idx, n+1)`. -/
theorem maybeUpdate_next_idx (p : Progress) (n : Nat) :
    (maybeUpdate p n).1.next_idx = Nat.max p.next_idx (n + 1) := by
  simp only [maybeUpdate]
  split <;> simp [Nat.max_comm]

/-- `maybeUpdate` preserves **INV-1**. -/
theorem maybeUpdate_valid (p : Progress) (n : Nat) (hv : valid p) :
    valid (maybeUpdate p n).1 := by
  simp only [valid, maybeUpdate]
  split <;> omega

/-- `maybeUpdate` is idempotent on `matched`: re-applying `n` doesn't change it. -/
theorem maybeUpdate_matched_idempotent (p : Progress) (n : Nat) :
    (maybeUpdate (maybeUpdate p n).1 n).1.matched = (maybeUpdate p n).1.matched := by
  simp only [maybeUpdate]
  split <;> split <;> omega

/-- Applying a stale `m ≤ matched` doesn't change `matched`. -/
theorem maybeUpdate_stale (p : Progress) (m : Nat) (hm : m ≤ p.matched) :
    (maybeUpdate p m).1.matched = p.matched := by
  simp only [maybeUpdate]
  split <;> omega

/-- If `maybeUpdate` returns `false`, `matched` is unchanged. -/
theorem maybeUpdate_false_matched (p : Progress) (n : Nat)
    (h : (maybeUpdate p n).2 = false) :
    (maybeUpdate p n).1.matched = p.matched := by
  simp only [maybeUpdate] at *
  split at h <;> simp_all

/-- After a genuine update (`true`), `paused` is cleared. -/
theorem maybeUpdate_true_unpaused (p : Progress) (n : Nat)
    (h : (maybeUpdate p n).2 = true) :
    (maybeUpdate p n).1.paused = false := by
  simp only [maybeUpdate] at *
  split at h <;> simp_all

/-- `next_idx` never decreases under `maybeUpdate`. -/
theorem maybeUpdate_next_idx_mono (p : Progress) (n : Nat) :
    p.next_idx ≤ (maybeUpdate p n).1.next_idx := by
  simp only [maybeUpdate]
  split <;> omega

/-- `matched` never decreases under `maybeUpdate`. -/
theorem maybeUpdate_matched_mono (p : Progress) (n : Nat) :
    p.matched ≤ (maybeUpdate p n).1.matched := by
  simp only [maybeUpdate]
  split <;> omega

/-- `maybeUpdate` doesn't change `state`. -/
theorem maybeUpdate_state (p : Progress) (n : Nat) :
    (maybeUpdate p n).1.state = p.state := by
  simp [maybeUpdate]
  split <;> simp

/-! ## Theorems about state transitions -/

/-- `becomeProbe` produces state `Probe`. -/
theorem becomeProbe_state (p : Progress) : (becomeProbe p).state = .Probe := by
  unfold becomeProbe resetState
  split <;> simp

/-- `becomeReplicate` produces state `Replicate`. -/
theorem becomeReplicate_state (p : Progress) : (becomeReplicate p).state = .Replicate := by
  simp [becomeReplicate, resetState]

/-- `becomeSnapshot` produces state `Snapshot`. -/
theorem becomeSnapshot_state (p : Progress) (idx : Nat) :
    (becomeSnapshot p idx).state = .Snapshot := by
  simp [becomeSnapshot, resetState]

/-- `becomeProbe` clears `paused`. -/
theorem becomeProbe_not_paused (p : Progress) : (becomeProbe p).paused = false := by
  unfold becomeProbe resetState
  split <;> simp

/-- `becomeReplicate` clears `paused`. -/
theorem becomeReplicate_not_paused (p : Progress) : (becomeReplicate p).paused = false := by
  simp [becomeReplicate, resetState]

/-- `becomeProbe` clears `pending_snapshot`. -/
theorem becomeProbe_no_pending (p : Progress) : (becomeProbe p).pending_snapshot = 0 := by
  unfold becomeProbe resetState
  split <;> simp

/-- `becomeReplicate` clears `pending_snapshot`. -/
theorem becomeReplicate_no_pending (p : Progress) : (becomeReplicate p).pending_snapshot = 0 := by
  simp [becomeReplicate, resetState]

/-- `becomeSnapshot` stores the given snapshot index. -/
theorem becomeSnapshot_pending (p : Progress) (idx : Nat) :
    (becomeSnapshot p idx).pending_snapshot = idx := by
  simp [becomeSnapshot, resetState]

/-- `becomeProbe` preserves **INV-1** (always `next_idx ≥ matched+1`). -/
theorem becomeProbe_valid (p : Progress) : valid (becomeProbe p) := by
  unfold valid becomeProbe resetState
  split <;> simp <;> omega

/-- `becomeReplicate` preserves **INV-1**. -/
theorem becomeReplicate_valid (p : Progress) : valid (becomeReplicate p) := by
  simp [valid, becomeReplicate, resetState]

/-- `becomeSnapshot` preserves **INV-1** (doesn't touch `matched`/`next_idx`). -/
theorem becomeSnapshot_valid (p : Progress) (idx : Nat) (hv : valid p) :
    valid (becomeSnapshot p idx) := by
  simp [valid, becomeSnapshot, resetState]
  exact hv

/-- After `becomeSnapshot`, `isPaused = true`. -/
theorem becomeSnapshot_paused (p : Progress) (idx : Nat) :
    isPaused (becomeSnapshot p idx) = true := by
  simp [isPaused, becomeSnapshot, resetState]

/-- After `becomeReplicate`, `isPaused = false`. -/
theorem becomeReplicate_isPaused_false (p : Progress) :
    isPaused (becomeReplicate p) = false := by
  simp [isPaused, becomeReplicate, resetState]

/-- After `becomeProbe`, `isPaused = false` (paused is cleared). -/
theorem becomeProbe_isPaused_false (p : Progress) :
    isPaused (becomeProbe p) = false := by
  unfold isPaused becomeProbe resetState
  split <;> simp

/-- `becomeProbe` from Snapshot: `next_idx = max(matched+1, pending_snapshot+1)`. -/
theorem becomeProbe_from_snapshot (p : Progress) (hs : p.state = .Snapshot) :
    (becomeProbe p).next_idx = Nat.max (p.matched + 1) (p.pending_snapshot + 1) := by
  subst hs
  simp [becomeProbe, resetState]

/-- `becomeProbe` from non-Snapshot: `next_idx = matched + 1`. -/
theorem becomeProbe_from_non_snapshot (p : Progress) (hs : p.state ≠ .Snapshot) :
    (becomeProbe p).next_idx = p.matched + 1 := by
  unfold becomeProbe resetState
  split
  · simp_all  -- p.state = .Snapshot contradicts hs
  · simp

/-- `becomeReplicate` sets `next_idx = matched + 1`. -/
theorem becomeReplicate_next_idx (p : Progress) :
    (becomeReplicate p).next_idx = p.matched + 1 := by
  simp [becomeReplicate, resetState]

/-! ## Theorems about `maybeDecrTo` -/

/-- `maybeDecrTo` preserves **INV-1** in Replicate state. -/
theorem maybeDecrTo_valid_replicate (p : Progress) (rejected matchHint : Nat)
    (hv : valid p) (hs : p.state = .Replicate) :
    valid (maybeDecrTo p rejected matchHint).1 := by
  simp only [valid, maybeDecrTo, hs]
  split <;> omega

/-- `maybeDecrTo` preserves **INV-1** in non-Replicate states. -/
theorem maybeDecrTo_valid_other (p : Progress) (rejected matchHint : Nat)
    (hv : valid p) (hs : p.state ≠ .Replicate) :
    valid (maybeDecrTo p rejected matchHint).1 := by
  unfold maybeDecrTo valid at *
  split
  · simp_all  -- p.state = .Replicate contradicts hs
  · split <;> omega

/-- When `maybeDecrTo` returns `false`, the progress is unchanged. -/
theorem maybeDecrTo_false_noop (p : Progress) (rejected matchHint : Nat)
    (h : (maybeDecrTo p rejected matchHint).2 = false) :
    (maybeDecrTo p rejected matchHint).1 = p := by
  unfold maybeDecrTo at *
  split at h ⊢ <;> split at h <;> simp_all

/-- In Replicate state, stale rejection leaves progress unchanged. -/
theorem maybeDecrTo_stale_replicate (p : Progress) (rejected matchHint : Nat)
    (hs : p.state = .Replicate) (hstale : rejected ≤ p.matched) :
    (maybeDecrTo p rejected matchHint).1 = p := by
  simp [maybeDecrTo, hs, hstale]

/-- In Replicate state with a fresh rejection, `next_idx` rolls back to
    `matched + 1`. -/
theorem maybeDecrTo_replicate_rollback (p : Progress) (rejected matchHint : Nat)
    (hs : p.state = .Replicate) (hfresh : p.matched < rejected) :
    (maybeDecrTo p rejected matchHint).1.next_idx = p.matched + 1 := by
  simp [maybeDecrTo, hs]
  omega

/-- `maybeDecrTo` never lowers `next_idx` below `matched + 1`. -/
theorem maybeDecrTo_next_idx_ge (p : Progress) (rejected matchHint : Nat)
    (hv : valid p) :
    p.matched + 1 ≤ (maybeDecrTo p rejected matchHint).1.next_idx := by
  simp only [valid] at hv
  unfold maybeDecrTo
  split <;> split <;> omega

/-! ## Composition theorems -/

/-- After `becomeReplicate`, a genuine `maybeUpdate(n ≥ matched)` advances
    `matched` to `n`. -/
theorem becomeReplicate_then_update (p : Progress) (n : Nat)
    (hn : p.matched ≤ n) :
    let p' := becomeReplicate p
    (maybeUpdate p' n).1.matched = n := by
  simp only [maybeUpdate, becomeReplicate, resetState]
  omega

/-- Applying `maybeUpdate(n₁)` then `maybeUpdate(n₂)` with `n₂ ≥ n₁` gives
    the same `matched` as applying `maybeUpdate(n₂)` directly. -/
theorem maybeUpdate_compose_matched (p : Progress) (n₁ n₂ : Nat) (h : n₁ ≤ n₂) :
    (maybeUpdate (maybeUpdate p n₁).1 n₂).1.matched = (maybeUpdate p n₂).1.matched := by
  simp only [maybeUpdate]
  split <;> split <;> split <;> omega

/-- After a sequence of updates with indices `≤ n`, the final `matched = n`
    (when starting with `matched ≤ n`). -/
theorem maybeUpdate_to_max (p : Progress) (n : Nat) (hn : p.matched ≤ n) :
    (maybeUpdate p n).1.matched = n := by
  simp only [maybeUpdate]
  split <;> omega

/-! ## Notes -/

/-
**Proof status (Tasks 1, 2, 3, 4)**:

Operations (0 sorry):
- `maybeUpdate`, `becomeProbe`, `becomeReplicate`, `becomeSnapshot`: ✅ defined
- `optimisticUpdate`, `maybeDecrTo`, `isPaused`: ✅ defined

Decidable examples: ✅ all pass with `decide`

Theorems proved (0 sorry, ~30 theorems):
- `maybeUpdate_returns_true_iff`
- `maybeUpdate_matched`, `maybeUpdate_next_idx`
- `maybeUpdate_valid` (INV-1 preserved)
- `maybeUpdate_matched_idempotent`, `maybeUpdate_stale`
- `maybeUpdate_false_matched`, `maybeUpdate_true_unpaused`
- `maybeUpdate_next_idx_mono`, `maybeUpdate_matched_mono`, `maybeUpdate_state`
- State result: `becomeProbe_state`, `becomeReplicate_state`, `becomeSnapshot_state`
- Paused: `becomeProbe_not_paused`, `becomeReplicate_not_paused`
- Pending: `becomeProbe_no_pending`, `becomeReplicate_no_pending`, `becomeSnapshot_pending`
- Validity: `becomeProbe_valid`, `becomeReplicate_valid`, `becomeSnapshot_valid`
- isPaused: `becomeSnapshot_paused`, `becomeReplicate_isPaused_false`, `becomeProbe_isPaused_false`
- next_idx: `becomeProbe_from_snapshot`, `becomeProbe_from_non_snapshot`, `becomeReplicate_next_idx`
- `maybeDecrTo_valid_replicate`, `maybeDecrTo_valid_other`
- `maybeDecrTo_false_noop`, `maybeDecrTo_stale_replicate`, `maybeDecrTo_replicate_rollback`
- `maybeDecrTo_next_idx_ge` (never lowers next_idx below matched+1)
- `becomeReplicate_then_update`, `maybeUpdate_compose_matched`, `maybeUpdate_to_max`

Deferred (future runs):
- `maybeDecrTo` with `request_snapshot` path
- `update_committed` monotonicity
- Composition with Inflights model for `isPaused` in Replicate mode
- `u64` overflow (Nat used instead)
- `maybe_decr_to` in non-Replicate: full case analysis including match_hint bounds
-/

end FVSquad.Progress
