/-!
# RaftLogRestore — Lean 4 Specification and Implementation Model

Formal specification of `RaftLog::restore(snapshot)` from `raft-rs` (`src/raft_log.rs`),
which delegates to `Unstable::restore` (`src/log_unstable.rs`).

`restore(snapshot)` installs a Raft snapshot as the new authoritative state of the log:
1. Asserts `snapshot.index >= self.committed` (snapshots may not roll back commits).
2. Clamps `self.persisted` to `min(committed_old, persisted_old)` when `persisted > committed`.
3. Advances `self.committed` to `snapshot.index`.
4. Clears all unstable entries, sets `unstable.offset = snapshot.index + 1`, stores
   the snapshot as the pending unstable snapshot.

## Model scope and approximations

* **Indices and terms**: `u64` → `Nat` (no overflow modelling).
* **Fields modelled**: `committed`, `persisted`, `unstable.offset`, `unstable.snapIndex`.
  `applied` and `store` are not modified by `restore` and are excluded from the model.
* **`unstable.entries`**: only their absence is modelled (after restore, entries = `[]`).
  We track `hasNoEntries : Bool` as a boolean flag.
* **Snapshot abstraction**: the snapshot is modelled as a pair `(snapIndex, snapTerm)`.
* **Panic**: the `assert!(index >= self.committed)` is captured as a precondition;
  behavior when violated is not modelled.
* **Logging**: the `info!` call is omitted.
* **`applied`**: not modified; excluded from the model. Invariant `applied ≤ committed`
  is noted as an open question in the informal spec (may be temporarily violated with
  `max_apply_unpersisted_log_limit > 0`).

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace FVSquad.RaftLogRestore

/-! ## State Model -/

/-- Abstract model of the fields relevant to `RaftLog::restore` and `Unstable::restore`. -/
structure RestoreState where
  /-- `self.committed`: highest log index known committed on a quorum. -/
  committed     : Nat
  /-- `self.persisted`: highest log index durably persisted on this node. -/
  persisted     : Nat
  /-- `self.unstable.offset`: first index in the in-memory (unstable) buffer. -/
  unstableOffset : Nat
  /-- `self.unstable.snapshot.map(_.index)`: index of any pending unstable snapshot. -/
  unstableSnap  : Option Nat

/-- A snapshot is modelled as its `(index, term)` metadata. -/
structure Snap where
  index : Nat
  term  : Nat

/-- **Precondition** for `restore`: the snapshot index must be ≥ committed.
    Violation triggers `assert!` panic in Rust. -/
def precondition (s : RestoreState) (snap : Snap) : Prop :=
  snap.index ≥ s.committed

/-- **WF**: invariants on `RestoreState` that hold in the real implementation
    under normal (non-panicking) conditions. -/
def RestoreState.WF (s : RestoreState) : Prop :=
  s.persisted < s.unstableOffset

/-! ## Implementation Model -/

/-- `unstableRestore snap`: functional model of `Unstable::restore(snap)`.

    Clears entries (`hasNoEntries` = true), advances offset to `snap.index + 1`,
    stores the snapshot. -/
def unstableRestore (snap : Snap) : (Nat × Option Nat) :=
  -- returns (new offset, new snapIndex)
  (snap.index + 1, some snap.index)

/-- `raftlogRestore s snap`: functional model of `RaftLog::restore(snapshot)`.

    Returns the new `RestoreState`.  Requires `precondition s snap`. -/
def raftlogRestore (s : RestoreState) (snap : Snap) : RestoreState :=
  let persistedNew := if s.persisted > s.committed then s.committed else s.persisted
  let (offsetNew, snapNew) := unstableRestore snap
  { committed     := snap.index
    persisted     := persistedNew
    unstableOffset := offsetNew
    unstableSnap  := snapNew }

/-! ## Key Properties -/

/-- **PROP-1 committed-advance**: `committed` is set to `snap.index`. -/
theorem committed_set (s : RestoreState) (snap : Snap) (h : precondition s snap) :
    (raftlogRestore s snap).committed = snap.index := by
  simp [raftlogRestore, unstableRestore]

/-- **PROP-2 committed-monotone**: `committed` never decreases. -/
theorem committed_monotone (s : RestoreState) (snap : Snap) (h : precondition s snap) :
    (raftlogRestore s snap).committed ≥ s.committed := by
  simp [raftlogRestore, unstableRestore]
  exact h

/-- **PROP-3 offset-set**: `unstableOffset` = `snap.index + 1` = `committed' + 1`. -/
theorem offset_set (s : RestoreState) (snap : Snap) :
    (raftlogRestore s snap).unstableOffset = snap.index + 1 := by
  simp [raftlogRestore, unstableRestore]

/-- **PROP-4 offset-eq-committed-succ**: after restore, `offset = committed + 1`. -/
theorem offset_eq_committed_succ (s : RestoreState) (snap : Snap) :
    (raftlogRestore s snap).unstableOffset = (raftlogRestore s snap).committed + 1 := by
  simp [raftlogRestore, unstableRestore]

/-- **PROP-5 snap-stored**: the unstable snapshot index is set to `snap.index`. -/
theorem snap_stored (s : RestoreState) (snap : Snap) :
    (raftlogRestore s snap).unstableSnap = some snap.index := by
  simp [raftlogRestore, unstableRestore]

/-- **PROP-6 persisted-clamped**: `persisted'` = `min(committed_old, persisted_old)`.

    When `persisted > committed`, it is clamped to `committed`; otherwise unchanged. -/
theorem persisted_clamped (s : RestoreState) (snap : Snap) :
    (raftlogRestore s snap).persisted = min s.committed s.persisted := by
  simp [raftlogRestore, unstableRestore, min_def]
  split_ifs with h
  · -- h : s.persisted > s.committed, i.e. s.committed < s.persisted
    omega
  · -- h : ¬ (s.persisted > s.committed)
    omega

/-- **PROP-7 persisted-le-committed**: `persisted' ≤ committed'` after restore.

    This is the crucial invariant: persisted entries never exceed committed. -/
theorem persisted_le_committed (s : RestoreState) (snap : Snap) (h : precondition s snap) :
    (raftlogRestore s snap).persisted ≤ (raftlogRestore s snap).committed := by
  simp [raftlogRestore, unstableRestore, precondition] at *
  split_ifs with hp
  · -- hp: s.persisted > s.committed; persisted' = s.committed ≤ snap.index
    omega
  · -- hp: s.persisted ≤ s.committed ≤ snap.index
    omega

/-- **PROP-8 persisted-lt-offset**: `persisted' < unstableOffset'`.

    This Lean invariant (`persisted < unstable.offset`) is preserved by restore. -/
theorem persisted_lt_offset (s : RestoreState) (snap : Snap) (h : precondition s snap) :
    (raftlogRestore s snap).persisted < (raftlogRestore s snap).unstableOffset := by
  simp [raftlogRestore, unstableRestore, precondition] at *
  split_ifs with hp <;> omega

/-- **PROP-9 wf-preserved**: if the state satisfies WF before restore, it satisfies WF after. -/
theorem wf_preserved (s : RestoreState) (snap : Snap) (h : precondition s snap)
    (_ : s.WF) :
    (raftlogRestore s snap).WF := by
  simp [RestoreState.WF]
  exact persisted_lt_offset s snap h

/-- **PROP-10 persisted-unchanged-when-le**: when `persisted ≤ committed`,
    `persisted` is not reset (it stays at `persisted_old`). -/
theorem persisted_unchanged_when_le (s : RestoreState) (snap : Snap)
    (h : s.persisted ≤ s.committed) :
    (raftlogRestore s snap).persisted = s.persisted := by
  simp [raftlogRestore, unstableRestore]
  omega

/-- **PROP-11 persisted-reset-when-gt**: when `persisted > committed`,
    `persisted` is reset to `committed_old`. -/
theorem persisted_reset_when_gt (s : RestoreState) (snap : Snap)
    (h : s.persisted > s.committed) :
    (raftlogRestore s snap).persisted = s.committed := by
  simp [raftlogRestore, unstableRestore]
  omega

/-- **PROP-12 idempotent-snap**: calling restore twice with the same snapshot
    yields the same state as calling it once. -/
theorem idempotent_snap (s : RestoreState) (snap : Snap) (h : precondition s snap) :
    let s' := raftlogRestore s snap
    have h' : precondition s' snap := by
      simp [precondition, raftlogRestore, unstableRestore]
    raftlogRestore s' snap = s' := by
  simp [raftlogRestore, unstableRestore, precondition] at *
  split_ifs with hp
  · simp [RestoreState.mk.injEq]
    constructor
    · rfl
    · split_ifs with hp2
      · -- snap.index > snap.index — contradiction
        omega
      · rfl
  · simp [RestoreState.mk.injEq]
    split_ifs with hp2
    · omega
    · rfl

/-! ## Concrete examples (sanity checks) -/

-- Example 1 from `test_restore_snap` (lines 1868-1876): persisted ≤ committed
-- Before: committed=100, persisted=100, offset=101
-- restore(snap(200, 1))
-- After:  committed=200, persisted=100, offset=201
#eval
  let s : RestoreState := { committed := 100, persisted := 100, unstableOffset := 101, unstableSnap := none }
  let snap : Snap := { index := 200, term := 1 }
  let s' := raftlogRestore s snap
  (s'.committed, s'.persisted, s'.unstableOffset, s'.unstableSnap)
  -- Expected: (200, 100, 201, some 200)

-- Example 2 from `test_restore_snap` (lines 1893-1896): persisted > committed
-- Before: committed=200, persisted=209, offset=210
-- restore(snap(205, 1))
-- After:  committed=205, persisted=200 (reset!), offset=206
#eval
  let s : RestoreState := { committed := 200, persisted := 209, unstableOffset := 210, unstableSnap := none }
  let snap : Snap := { index := 205, term := 1 }
  let s' := raftlogRestore s snap
  (s'.committed, s'.persisted, s'.unstableOffset, s'.unstableSnap)
  -- Expected: (205, 200, 206, some 205)

-- Example 3: snap.index == committed (minimal advance)
#eval
  let s : RestoreState := { committed := 50, persisted := 50, unstableOffset := 51, unstableSnap := none }
  let snap : Snap := { index := 50, term := 2 }
  let s' := raftlogRestore s snap
  (s'.committed, s'.persisted, s'.unstableOffset, s'.unstableSnap)
  -- Expected: (50, 50, 51, some 50)

-- Verify PROP-7 (persisted ≤ committed) on both examples
example : (raftlogRestore
    { committed := 100, persisted := 100, unstableOffset := 101, unstableSnap := none }
    { index := 200, term := 1 }).persisted ≤
  (raftlogRestore
    { committed := 100, persisted := 100, unstableOffset := 101, unstableSnap := none }
    { index := 200, term := 1 }).committed := by
  native_decide

example : (raftlogRestore
    { committed := 200, persisted := 209, unstableOffset := 210, unstableSnap := none }
    { index := 205, term := 1 }).persisted ≤
  (raftlogRestore
    { committed := 200, persisted := 209, unstableOffset := 210, unstableSnap := none }
    { index := 205, term := 1 }).committed := by
  native_decide

end FVSquad.RaftLogRestore
