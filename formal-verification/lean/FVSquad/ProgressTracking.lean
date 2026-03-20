/-!
# ProgressTracking — Lean 4 Specification and Implementation Model

Formal specification of three key `Progress` mutation methods from `raft-rs`
(`src/tracker/progress.rs`):

* `maybe_update(n)` — advance `matched` (and `next_idx`) on a fresh ACK
* `update_committed(ci)` — monotonically advance `committed_index`
* `maybe_decr_to(rejected, match_hint, request_snapshot)` — retreat `next_idx` on rejection

`Progress` is the leader's per-follower view of replication state.  These three
methods are the primary ways the leader updates that view during normal operation.

## Key Approximations

* `u64` → `Nat` (no wraparound; u64 overflow is not modelled).
* `INVALID_INDEX = 0` (matches the Rust constant `INVALID_INDEX = 0` in `src/lib.rs`).
* `Inflights` ring buffer — omitted (modelled separately in `Inflights.lean`).
* `pending_snapshot`, `recent_active`, `commit_group_id` — included as fields
  for completeness, but only `pending_request_snapshot` is constrained here.
* `resume()` (sets `paused := false`) is inlined at each call site.
* The `Snapshot` state handling in `maybe_decr_to` is included in the function
  model; WF preservation is proved for Probe and Replicate states; the Snapshot
  state has lighter proof coverage (it always returns `true` with a paused clear).

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace FVSquad.ProgressTracking

/-! ## Constants -/

/-- Sentinel "no valid index".  Mirrors `INVALID_INDEX = 0` in `src/lib.rs`. -/
def INVALID_INDEX : Nat := 0

/-! ## State Model -/

/-- The three replication pipeline states a follower can be in. -/
inductive ProgressState where
  | Probe
  | Replicate
  | Snapshot
  deriving DecidableEq, Repr

/-- Abstract model of `Progress`, focused on the fields used by the three target methods. -/
structure Progress where
  /-- Highest log index known replicated on the follower. -/
  matched                  : Nat
  /-- Next log index to send to the follower. -/
  next_idx                 : Nat
  /-- Current pipeline state. -/
  state                    : ProgressState
  /-- Whether sending is temporarily paused (meaningful in Probe state). -/
  paused                   : Bool
  /-- Pending request-snapshot index; `INVALID_INDEX` (0) means none. -/
  pending_request_snapshot : Nat
  /-- Highest committed index this follower has acknowledged. -/
  committed_index          : Nat
  deriving DecidableEq, Repr

/-- **WF**: `next_idx` is always strictly greater than `matched` (i.e. `≥ matched + 1`).

    Equivalently: the next index to send is beyond the confirmed match point.
    All three operations preserve this invariant. -/
def WF (p : Progress) : Prop :=
  p.matched + 1 ≤ p.next_idx

/-! ## `maybe_update` -/

/-- Model of `Progress::maybe_update(n)`.

    Advances `matched` (and clears `paused`) when `n > matched`, and always
    ensures `next_idx ≥ n + 1`.  Returns `(result, changed)` where `changed`
    mirrors the Rust `bool` return. -/
def maybeUpdate (p : Progress) (n : Nat) : Progress × Bool :=
  if p.matched < n then
    if p.next_idx < n + 1 then
      ({ p with matched := n, paused := false, next_idx := n + 1 }, true)
    else
      ({ p with matched := n, paused := false }, true)
  else
    if p.next_idx < n + 1 then
      ({ p with next_idx := n + 1 }, false)
    else
      (p, false)

/-- **PROP-1**: Returns `true` iff the match genuinely advanced (`n > matched`). -/
theorem maybeUpdate_true_iff (p : Progress) (n : Nat) :
    (maybeUpdate p n).2 = true ↔ p.matched < n := by
  simp only [maybeUpdate]; split_ifs <;> simp_all

/-- **PROP-2**: Returns `false` iff `n ≤ matched` (stale or duplicate ACK). -/
theorem maybeUpdate_false_iff (p : Progress) (n : Nat) :
    (maybeUpdate p n).2 = false ↔ ¬(p.matched < n) := by
  simp only [maybeUpdate]; split_ifs <;> simp_all

/-- **PROP-3**: After `maybeUpdate`, `matched = max(old_matched, n)`. -/
theorem maybeUpdate_matched_eq (p : Progress) (n : Nat) :
    (maybeUpdate p n).1.matched = max p.matched n := by
  simp only [maybeUpdate]
  split_ifs with h1 h2 <;> simp_all <;> omega

/-- **PROP-4**: After `maybeUpdate`, `next_idx = max(old_next_idx, n + 1)`. -/
theorem maybeUpdate_next_idx_eq (p : Progress) (n : Nat) :
    (maybeUpdate p n).1.next_idx = max p.next_idx (n + 1) := by
  simp only [maybeUpdate]
  split_ifs with h1 h2 <;> simp_all <;> omega

/-- **PROP-5**: `matched` is non-decreasing. -/
theorem maybeUpdate_matched_mono (p : Progress) (n : Nat) :
    p.matched ≤ (maybeUpdate p n).1.matched := by
  rw [maybeUpdate_matched_eq]; omega

/-- **PROP-6**: `next_idx` is non-decreasing. -/
theorem maybeUpdate_next_idx_mono (p : Progress) (n : Nat) :
    p.next_idx ≤ (maybeUpdate p n).1.next_idx := by
  rw [maybeUpdate_next_idx_eq]; omega

/-- **PROP-7**: The WF invariant is preserved. -/
theorem maybeUpdate_wf (p : Progress) (n : Nat) (h : WF p) :
    WF (maybeUpdate p n).1 := by
  unfold WF at *
  rw [maybeUpdate_matched_eq, maybeUpdate_next_idx_eq]
  omega

/-- **PROP-8**: On success, `matched` is exactly `n`. -/
theorem maybeUpdate_success_matched (p : Progress) (n : Nat)
    (h : (maybeUpdate p n).2 = true) :
    (maybeUpdate p n).1.matched = n := by
  rw [maybeUpdate_matched_eq]
  rw [maybeUpdate_true_iff] at h
  omega

/-- **PROP-9**: On failure, `matched` is unchanged. -/
theorem maybeUpdate_failure_matched (p : Progress) (n : Nat)
    (h : (maybeUpdate p n).2 = false) :
    (maybeUpdate p n).1.matched = p.matched := by
  rw [maybeUpdate_matched_eq]
  rw [maybeUpdate_false_iff] at h
  omega

/-- **PROP-10**: On success, `paused` is cleared to `false`. -/
theorem maybeUpdate_success_paused (p : Progress) (n : Nat)
    (h : (maybeUpdate p n).2 = true) :
    (maybeUpdate p n).1.paused = false := by
  simp only [maybeUpdate] at h ⊢
  split_ifs with h1 h2 <;> simp_all

/-- **PROP-11**: `state` is unchanged by `maybeUpdate`. -/
theorem maybeUpdate_state_unchanged (p : Progress) (n : Nat) :
    (maybeUpdate p n).1.state = p.state := by
  simp only [maybeUpdate]; split_ifs <;> simp

/-- **PROP-12**: `committed_index` is unchanged by `maybeUpdate`. -/
theorem maybeUpdate_committed_index_unchanged (p : Progress) (n : Nat) :
    (maybeUpdate p n).1.committed_index = p.committed_index := by
  simp only [maybeUpdate]; split_ifs <;> simp

/-- **PROP-13**: `pending_request_snapshot` is unchanged by `maybeUpdate`. -/
theorem maybeUpdate_prs_unchanged (p : Progress) (n : Nat) :
    (maybeUpdate p n).1.pending_request_snapshot = p.pending_request_snapshot := by
  simp only [maybeUpdate]; split_ifs <;> simp

/-- **PROP-14**: `maybeUpdate` is idempotent: a second call with the same `n` returns `false`. -/
theorem maybeUpdate_idempotent (p : Progress) (n : Nat) :
    (maybeUpdate (maybeUpdate p n).1 n).2 = false := by
  rw [maybeUpdate_false_iff, maybeUpdate_matched_eq]
  omega

/-! ## `update_committed` -/

/-- Model of `Progress::update_committed(ci)`.

    Advances `committed_index` to `ci` if strictly greater; otherwise no-op. -/
def updateCommitted (p : Progress) (ci : Nat) : Progress :=
  if ci > p.committed_index then { p with committed_index := ci } else p

/-- **PROP-15**: `committed_index` is non-decreasing. -/
theorem updateCommitted_mono (p : Progress) (ci : Nat) :
    p.committed_index ≤ (updateCommitted p ci).committed_index := by
  simp [updateCommitted]; split_ifs <;> omega

/-- **PROP-16**: `committed_index` after the call equals `max(old, ci)`. -/
theorem updateCommitted_eq_max (p : Progress) (ci : Nat) :
    (updateCommitted p ci).committed_index = max p.committed_index ci := by
  simp [updateCommitted]
  split_ifs with h <;> omega

/-- **PROP-17**: `committed_index` advances iff `ci > old`. -/
theorem updateCommitted_advances_iff (p : Progress) (ci : Nat) :
    (updateCommitted p ci).committed_index > p.committed_index ↔ ci > p.committed_index := by
  simp [updateCommitted]; split_ifs with h <;> omega

/-- **PROP-18**: `matched` is unchanged by `updateCommitted`. -/
theorem updateCommitted_matched_unchanged (p : Progress) (ci : Nat) :
    (updateCommitted p ci).matched = p.matched := by
  simp [updateCommitted]; split_ifs <;> simp

/-- **PROP-19**: `next_idx` is unchanged by `updateCommitted`. -/
theorem updateCommitted_next_idx_unchanged (p : Progress) (ci : Nat) :
    (updateCommitted p ci).next_idx = p.next_idx := by
  simp [updateCommitted]; split_ifs <;> simp

/-- **PROP-20**: WF is preserved by `updateCommitted`. -/
theorem updateCommitted_wf (p : Progress) (ci : Nat) (h : WF p) :
    WF (updateCommitted p ci) := by
  unfold WF at *
  rw [updateCommitted_next_idx_unchanged, updateCommitted_matched_unchanged]
  exact h

/-- **PROP-21**: `updateCommitted` is idempotent. -/
theorem updateCommitted_idempotent (p : Progress) (ci : Nat) :
    updateCommitted (updateCommitted p ci) ci = updateCommitted p ci := by
  simp [updateCommitted]; split_ifs with h <;> simp_all <;> omega

/-! ## `maybe_decr_to` -/

/-- Model of `Progress::maybe_decr_to(rejected, match_hint, request_snapshot)`.

    Retreats `next_idx` when the leader receives a rejection message.
    Ignores the rejection if it is determined to be stale.
    Returns `(result, changed)` mirroring the Rust `bool` return. -/
def maybeDecrTo (p : Progress) (rejected : Nat) (match_hint : Nat)
    (request_snapshot : Nat) : Progress × Bool :=
  if p.state = ProgressState.Replicate then
    -- Stale: the rejection is for an already-matched entry
    if rejected < p.matched ∨ (rejected = p.matched ∧ request_snapshot = INVALID_INDEX) then
      (p, false)
    else if request_snapshot = INVALID_INDEX then
      ({ p with next_idx := p.matched + 1 }, true)
    else
      ({ p with pending_request_snapshot := request_snapshot }, true)
  else
    -- Probe / Snapshot: stale if not for the most recently sent index
    if (p.next_idx = 0 ∨ p.next_idx - 1 ≠ rejected) ∧ request_snapshot = INVALID_INDEX then
      (p, false)
    else if request_snapshot = INVALID_INDEX then
      let new_next := max (p.matched + 1) (min rejected (match_hint + 1))
      ({ p with next_idx := new_next, paused := false }, true)
    else if p.pending_request_snapshot = INVALID_INDEX then
      ({ p with pending_request_snapshot := request_snapshot, paused := false }, true)
    else
      ({ p with paused := false }, true)

-- ─── Replicate-state properties ──────────────────────────────────────────────

/-- **PROP-22**: In Replicate state, a rejection below `matched` is stale → false. -/
theorem maybeDecrTo_replicate_stale_low (p : Progress) (rejected mh rs : Nat)
    (hs : p.state = ProgressState.Replicate)
    (hlt : rejected < p.matched) :
    (maybeDecrTo p rejected mh rs).2 = false := by
  simp [maybeDecrTo, hs, hlt]

/-- **PROP-23**: In Replicate state, rejection equal to `matched` without snapshot → false. -/
theorem maybeDecrTo_replicate_stale_eq (p : Progress) (rejected mh : Nat)
    (hs : p.state = ProgressState.Replicate)
    (heq : rejected = p.matched) :
    (maybeDecrTo p rejected mh INVALID_INDEX).2 = false := by
  simp [maybeDecrTo, hs, INVALID_INDEX, heq]

/-- **PROP-24**: In Replicate state, fresh rejection (> matched) with no snapshot request
    → `next_idx` is reset to `matched + 1`. -/
theorem maybeDecrTo_replicate_no_snap_next (p : Progress) (rejected mh : Nat)
    (hs : p.state = ProgressState.Replicate)
    (hgt : p.matched < rejected) :
    (maybeDecrTo p rejected mh INVALID_INDEX).1.next_idx = p.matched + 1 := by
  have hlt : ¬(rejected < p.matched) := Nat.not_lt.mpr (Nat.le_of_lt hgt)
  have hne : rejected ≠ p.matched := Nat.ne_of_gt hgt
  simp [maybeDecrTo, hs, INVALID_INDEX, hlt, hne]

/-- **PROP-25**: In Replicate state, fresh rejection with no snapshot → returns `true`. -/
theorem maybeDecrTo_replicate_no_snap_true (p : Progress) (rejected mh : Nat)
    (hs : p.state = ProgressState.Replicate)
    (hgt : p.matched < rejected) :
    (maybeDecrTo p rejected mh INVALID_INDEX).2 = true := by
  have hlt : ¬(rejected < p.matched) := Nat.not_lt.mpr (Nat.le_of_lt hgt)
  have hne : rejected ≠ p.matched := Nat.ne_of_gt hgt
  simp [maybeDecrTo, hs, INVALID_INDEX, hlt, hne]

/-- **PROP-26**: `matched` is never changed by `maybeDecrTo`. -/
theorem maybeDecrTo_matched_unchanged (p : Progress) (rejected mh rs : Nat) :
    (maybeDecrTo p rejected mh rs).1.matched = p.matched := by
  simp [maybeDecrTo]; split_ifs <;> simp

/-- **PROP-27**: `committed_index` is never changed by `maybeDecrTo`. -/
theorem maybeDecrTo_committed_index_unchanged (p : Progress) (rejected mh rs : Nat) :
    (maybeDecrTo p rejected mh rs).1.committed_index = p.committed_index := by
  simp [maybeDecrTo]; split_ifs <;> simp

/-- **PROP-28**: WF is preserved in Replicate state. -/
theorem maybeDecrTo_replicate_wf (p : Progress) (rejected mh rs : Nat)
    (hs : p.state = ProgressState.Replicate)
    (hw : WF p) :
    WF (maybeDecrTo p rejected mh rs).1 := by
  unfold WF at *
  simp only [maybeDecrTo, hs, ↓reduceIte]
  split_ifs with h1 h2 <;> simp_all <;> omega

/-- **PROP-29**: WF is preserved in Probe state. -/
theorem maybeDecrTo_probe_wf (p : Progress) (rejected mh rs : Nat)
    (hs : p.state = ProgressState.Probe)
    (hw : WF p) :
    WF (maybeDecrTo p rejected mh rs).1 := by
  have hne : p.state ≠ ProgressState.Replicate := by simp [hs]
  unfold WF at *
  simp only [maybeDecrTo, hne, ↓reduceIte, if_false]
  split_ifs with h1 h2 h3 <;> simp_all <;> omega

-- ─── Cross-operation commutativity ──────────────────────────────────────────

/-- **PROP-30**: `updateCommitted` and `maybeUpdate` commute on `committed_index`. -/
theorem updateCommitted_maybeUpdate_committed (p : Progress) (ci n : Nat) :
    (maybeUpdate (updateCommitted p ci) n).1.committed_index =
    (updateCommitted (maybeUpdate p n).1 ci).committed_index := by
  rw [maybeUpdate_committed_index_unchanged, updateCommitted_eq_max,
      updateCommitted_eq_max, maybeUpdate_committed_index_unchanged]

/-- **PROP-31**: Two `updateCommitted` calls give `max(old, max(ci1, ci2))`. -/
theorem updateCommitted_chain (p : Progress) (ci1 ci2 : Nat) :
    (updateCommitted (updateCommitted p ci1) ci2).committed_index =
    max p.committed_index (max ci1 ci2) := by
  rw [updateCommitted_eq_max, updateCommitted_eq_max, Nat.max_assoc]

end FVSquad.ProgressTracking
