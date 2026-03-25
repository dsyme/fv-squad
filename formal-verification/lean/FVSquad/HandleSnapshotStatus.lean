/-!
# HandleSnapshotStatus — Lean 4 Specification, Implementation, and Proofs

Models `RaftCore::handle_snapshot_status` in `src/raft.rs` (lines ≈ 1980–2025):
the handler for `MsgSnapStatus` on the leader side, finalising a snapshot send.

## Relevant Rust code

```rust
fn handle_snapshot_status(&mut self, m: &Message) {
    let pr = match self.prs.get_mut(m.from) {
        Some(pr) => pr,
        None => { return; }
    };
    if pr.state != ProgressState::Snapshot {
        return;
    }
    if m.reject {
        pr.snapshot_failure();   // sets pending_snapshot = 0
        pr.become_probe();       // Snapshot -> Probe, next_idx = max(matched+1, 1)
    } else {
        pr.become_probe();       // Snapshot -> Probe, next_idx = max(matched+1, ps+1)
    }
    pr.pause();                              // paused = true
    pr.pending_request_snapshot = INVALID_INDEX;  // = 0
}
```

`become_probe` when coming from Snapshot state:
```rust
pub fn become_probe(&mut self) {
    if self.state == ProgressState::Snapshot {
        let pending_snapshot = self.pending_snapshot;
        self.reset_state(ProgressState::Probe);   // sets pending_snapshot=0, paused=false
        self.next_idx = cmp::max(self.matched + 1, pending_snapshot + 1);
    } else { ... }
}
```

## Model scope and approximations

* We model only the progress-update aspect; no message routing, logging, or network.
* `INVALID_INDEX = 0` in TiKV raft; modelled directly as `0 : Nat`.
* Inflight windows are abstracted — `pause` only concerns `paused : Bool`.
* The "unknown peer" early-return path is modelled as `Option` at the call site.
* We model the state machine only for progress entries in `ProgressState.Snapshot`.

🔬 *Lean Squad — automated formal verification.*
-/

import Mathlib.Tactic

namespace FVSquad.HandleSnapshotStatus

/-! ## Types -/

/-- Progress state for a peer, as seen by the leader. -/
inductive ProgressState where
  | Probe
  | Replicate
  | Snapshot
  deriving DecidableEq, Repr

/-- Progress entry for a single peer during snapshot handling.
    We include only the fields relevant to `handle_snapshot_status`. -/
structure SnapProgress where
  /-- Current replication state. -/
  state                    : ProgressState
  /-- Highest index known to be replicated on peer. -/
  matched                  : Nat
  /-- Next index to send to peer. -/
  next_idx                 : Nat
  /-- Index of the in-flight snapshot. -/
  pending_snapshot         : Nat
  /-- Index of a pending snapshot requested by the peer. `0` = INVALID_INDEX. -/
  pending_request_snapshot : Nat
  /-- Whether probing is paused (waiting for ACK before next send). -/
  paused                   : Bool
  deriving Repr

/-! ## Implementation model -/

/-- `snapshot_failure`: clears `pending_snapshot`. -/
def snapshotFailure (p : SnapProgress) : SnapProgress :=
  { p with pending_snapshot := 0 }

/-- `become_probe` from Snapshot state.
    Saves the (old) `pending_snapshot` before `reset_state` clears it. -/
def becomeProbeFromSnapshot (p : SnapProgress) : SnapProgress :=
  let ps := p.pending_snapshot
  { p with
    state            := ProgressState.Probe
    pending_snapshot := 0
    paused           := false
    next_idx         := max (p.matched + 1) (ps + 1) }

/-- `pause`: sets `paused = true`. -/
def pauseProgress (p : SnapProgress) : SnapProgress :=
  { p with paused := true }

/-- Pure model of the body of `handle_snapshot_status`, given a peer progress entry
    that is confirmed to be in `ProgressState.Snapshot`.
    Returns the updated progress. -/
def handleSnapshotStatus (reject : Bool) (p : SnapProgress) : SnapProgress :=
  let p' :=
    if reject then
      becomeProbeFromSnapshot (snapshotFailure p)
    else
      becomeProbeFromSnapshot p
  let p'' := pauseProgress p'
  { p'' with pending_request_snapshot := 0 }

/-! ## Core lemmas about individual operations -/

@[simp]
theorem snapshotFailure_clears_pending (p : SnapProgress) :
    (snapshotFailure p).pending_snapshot = 0 := by
  simp [snapshotFailure]

@[simp]
theorem snapshotFailure_preserves_matched (p : SnapProgress) :
    (snapshotFailure p).matched = p.matched := by
  simp [snapshotFailure]

@[simp]
theorem snapshotFailure_preserves_state (p : SnapProgress) :
    (snapshotFailure p).state = p.state := by
  simp [snapshotFailure]

@[simp]
theorem becomeProbe_state (p : SnapProgress) :
    (becomeProbeFromSnapshot p).state = ProgressState.Probe := by
  simp [becomeProbeFromSnapshot]

@[simp]
theorem becomeProbe_pending_snapshot (p : SnapProgress) :
    (becomeProbeFromSnapshot p).pending_snapshot = 0 := by
  simp [becomeProbeFromSnapshot]

@[simp]
theorem becomeProbe_paused (p : SnapProgress) :
    (becomeProbeFromSnapshot p).paused = false := by
  simp [becomeProbeFromSnapshot]

@[simp]
theorem becomeProbe_next_idx (p : SnapProgress) :
    (becomeProbeFromSnapshot p).next_idx = max (p.matched + 1) (p.pending_snapshot + 1) := by
  simp [becomeProbeFromSnapshot]

/-- On failure path: `pending_snapshot` is cleared before `become_probe`,
    so `next_idx` is `matched + 1` (since `max(matched+1, 0+1) = matched+1`). -/
theorem becomeProbe_after_failure_next_idx (p : SnapProgress) :
    (becomeProbeFromSnapshot (snapshotFailure p)).next_idx = p.matched + 1 := by
  simp [becomeProbeFromSnapshot, snapshotFailure]
  omega

/-- On success path: `next_idx` is `max(matched+1, pending_snapshot+1)`. -/
theorem becomeProbe_success_next_idx (p : SnapProgress) :
    (becomeProbeFromSnapshot p).next_idx = max (p.matched + 1) (p.pending_snapshot + 1) := by
  simp [becomeProbeFromSnapshot]

/-! ## Main theorems about `handleSnapshotStatus` -/

/-- **T1** After handling, state is always `Probe`. -/
theorem hss_state_is_probe (reject : Bool) (p : SnapProgress) :
    (handleSnapshotStatus reject p).state = ProgressState.Probe := by
  simp [handleSnapshotStatus, becomeProbeFromSnapshot, pauseProgress]
  cases reject <;> simp [snapshotFailure, becomeProbeFromSnapshot]

/-- **T2** After handling, the progress is always paused. -/
theorem hss_always_paused (reject : Bool) (p : SnapProgress) :
    (handleSnapshotStatus reject p).paused = true := by
  simp [handleSnapshotStatus, pauseProgress, becomeProbeFromSnapshot]
  cases reject <;> simp [snapshotFailure, becomeProbeFromSnapshot, pauseProgress]

/-- **T3** After handling, `pending_request_snapshot` is reset to `INVALID_INDEX` (0). -/
theorem hss_pending_request_snapshot_reset (reject : Bool) (p : SnapProgress) :
    (handleSnapshotStatus reject p).pending_request_snapshot = 0 := by
  simp [handleSnapshotStatus]

/-- **T4** After handling, `pending_snapshot` is always 0 (cleared by `become_probe`). -/
theorem hss_pending_snapshot_cleared (reject : Bool) (p : SnapProgress) :
    (handleSnapshotStatus reject p).pending_snapshot = 0 := by
  simp [handleSnapshotStatus, pauseProgress]
  cases reject <;> simp [snapshotFailure, becomeProbeFromSnapshot, pauseProgress]

/-- **T5** On reject: `next_idx = matched + 1`. -/
theorem hss_reject_next_idx (p : SnapProgress) :
    (handleSnapshotStatus true p).next_idx = p.matched + 1 := by
  simp [handleSnapshotStatus, becomeProbeFromSnapshot, snapshotFailure, pauseProgress]
  omega

/-- **T6** On success: `next_idx = max(matched+1, pending_snapshot+1)`. -/
theorem hss_success_next_idx (p : SnapProgress) :
    (handleSnapshotStatus false p).next_idx = max (p.matched + 1) (p.pending_snapshot + 1) := by
  simp [handleSnapshotStatus, becomeProbeFromSnapshot, pauseProgress]

/-- **T7** `matched` is never changed by `handle_snapshot_status`. -/
theorem hss_matched_unchanged (reject : Bool) (p : SnapProgress) :
    (handleSnapshotStatus reject p).matched = p.matched := by
  simp [handleSnapshotStatus, pauseProgress]
  cases reject <;> simp [snapshotFailure, becomeProbeFromSnapshot, pauseProgress]

/-- **T8** On success: `next_idx ≥ matched + 1` (invariant preserved). -/
theorem hss_success_next_ge_matched (p : SnapProgress) :
    (handleSnapshotStatus false p).next_idx ≥ p.matched + 1 := by
  rw [hss_success_next_idx]
  omega

/-- **T9** On reject: `next_idx ≥ matched + 1` (invariant preserved). -/
theorem hss_reject_next_ge_matched (p : SnapProgress) :
    (handleSnapshotStatus true p).next_idx ≥ p.matched + 1 := by
  rw [hss_reject_next_idx]

/-- **T10** In both cases: `next_idx ≥ matched + 1`. -/
theorem hss_next_ge_matched (reject : Bool) (p : SnapProgress) :
    (handleSnapshotStatus reject p).next_idx ≥ p.matched + 1 := by
  cases reject
  · exact hss_success_next_ge_matched p
  · exact hss_reject_next_ge_matched p

/-- **T11** On success: `next_idx ≥ old pending_snapshot + 1`
    (the follower will pick up from after the snapshot). -/
theorem hss_success_next_ge_snapshot (p : SnapProgress) :
    (handleSnapshotStatus false p).next_idx ≥ p.pending_snapshot + 1 := by
  rw [hss_success_next_idx]
  omega

/-- **T12** Reject and success paths differ only in `next_idx` when
    `pending_snapshot ≥ matched`.
    Specifically, on success `next_idx ≥ pending_snapshot + 1`,
    while on reject `next_idx = matched + 1`. -/
theorem hss_paths_diverge_on_pending (p : SnapProgress)
    (hps : p.pending_snapshot > p.matched) :
    (handleSnapshotStatus false p).next_idx > (handleSnapshotStatus true p).next_idx := by
  rw [hss_success_next_idx, hss_reject_next_idx]
  omega

/-- **T13** All three "reset" fields are cleared regardless of reject flag. -/
theorem hss_all_cleared (reject : Bool) (p : SnapProgress) :
    (handleSnapshotStatus reject p).pending_snapshot = 0 ∧
    (handleSnapshotStatus reject p).pending_request_snapshot = 0 := by
  exact ⟨hss_pending_snapshot_cleared reject p, hss_pending_request_snapshot_reset reject p⟩

end FVSquad.HandleSnapshotStatus
