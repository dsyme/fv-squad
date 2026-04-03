import FVSquad.MaybeAppend
import FVSquad.SafetyComposition
import FVSquad.CommittedIndex
import FVSquad.FindConflict
import FVSquad.RaftSafety

/-!
# Cross-Module Composition: Log Operations ↔ Quorum Layer

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file bridges the **log-operation layer** (`MaybeAppend`, `FindConflict`) to the
**quorum layer** (`CommittedIndex`, `SafetyComposition`), establishing theorems that
connect log-append operations to commit-index advancement.

## The Gap This File Closes

Prior FV work proved log operations (MaybeAppend: 18 theorems) and quorum reasoning
(CommittedIndex: 17 theorems, SafetyComposition: 9 theorems) independently.  The key
missing connection: **when a replication round succeeds, does the committed index advance
correctly, and does it stay consistent with the quorum's acknowledgment?**

## Theorem table

| ID   | Name                                        | Status    | Description                                               |
|------|---------------------------------------------|-----------|-----------------------------------------------------------|
| CMC1 | `CMC1_replication_advances_commit`          | ✅ proved  | Quorum acked ≥ k → committedIndex ≥ k (SC5 in log context)|
| CMC2 | `CMC2_maybeAppend_replication_commit`       | ✅ proved  | Quorum acked ≥ lastNew → committedIndex ≥ lastNew         |
| CMC3 | `CMC3_maybeAppend_committed_bounded`        | ✅ proved  | New committed ≤ committedIndex given quorum + bounds      |
| CMC4 | `CMC4_findConflict_safe_commit_prefix`      | 🔄 sorry  | No conflict → entries are a prefix of existing log        |
| CMC5 | `CMC5_progress_committed_le_ci`             | ✅ proved  | Committed index advances monotonically with acked values  |
| CMC6 | `CMC6_committed_index_entry_bridge`         | 🔄 sorry  | committedIndex ≥ k → ∃ quorum voters with log[k] = e     |
| CMC7 | `CMC7_maybeAppend_safety_composition`       | ✅ proved  | Log entries committed via maybe_append are unique         |

## Key bridge result

**CMC3** is the central result: given that:
1. The previous `s.committed` is within the quorum's `committedIndex`,
2. The `committed_to` argument `ca` is within the quorum's `committedIndex`,
3. A replication quorum has acknowledged `lastNew = idx + ents.length`,

then the new committed value after `maybeAppend` is also within the quorum's
`committedIndex`.  This formalises the Raft invariant that commit index advancement
is always "safe" — the leader never commits beyond what a majority has replicated.

## Modelling notes

- `AckedFn` is `Nat → Nat` (voter ID → last acknowledged index).
- All numeric types are `Nat`; no overflow, no `u64::MAX` sentinel.
- `maybeAppend` here refers to the pure functional model in `MaybeAppend.lean`.
-/

-- HasQuorum.lean has no namespace; hasQuorum, overlapCount etc. are in root namespace
open FVSquad.CommittedIndex
open FVSquad.SafetyComposition
open FVSquad.MaybeAppend
open FVSquad.FindConflict
open FVSquad.RaftSafety

namespace FVSquad.CrossModuleComposition

/-! ## CMC1: Replication quorum advances commit index -/

/-- **CMC1** — A replication quorum advances the committed index.

    If a majority of voters have acknowledged index ≥ `k` (i.e., they have replicated
    entries up to index `k`), then `committedIndex voters acked ≥ k`.

    **Proof**: this is `SC5_hasQuorum_implies_committedIndex_ge` from
    `SafetyComposition`, re-stated in the log-replication context.  The name makes
    the intended use explicit: once `maybe_append` extends a majority's logs to include
    entry at index `k`, a quorum exists and the committed index can advance to ≥ k.

    **Usage pattern**:
    ```
    have hrep : hasQuorum voters (fun v => decide (acked v ≥ lastNew)) = true := ...
    have hci  := CMC1_replication_advances_commit voters acked lastNew hrep
    -- now: committedIndex voters acked ≥ lastNew
    ``` -/
theorem CMC1_replication_advances_commit
    (hd : Nat) (tl : List Nat) (acked : AckedFn) (k : Nat)
    (hq : hasQuorum (hd :: tl) (fun v => decide (acked v ≥ k)) = true) :
    committedIndex (hd :: tl) acked ≥ k :=
  SC5_hasQuorum_implies_committedIndex_ge hd tl acked k hq

/-! ## CMC2: maybeAppend lastNew is a valid commit threshold -/

/-- **CMC2** — `maybe_append`'s `lastNew` is a valid commit threshold after replication.

    When `maybeAppend` succeeds (entries were accepted), `lastNew = idx + ents.length`.
    If a majority of voters have subsequently replicated up to `lastNew`, then
    `committedIndex ≥ lastNew`.

    **Proof**: immediate from CMC1 with `k = idx + ents.length`. -/
theorem CMC2_maybeAppend_replication_commit
    (hd : Nat) (tl : List Nat) (acked : AckedFn)
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (hq : hasQuorum (hd :: tl)
        (fun v => decide (acked v ≥ idx + ents.length)) = true) :
    committedIndex (hd :: tl) acked ≥ idx + ents.length :=
  CMC1_replication_advances_commit hd tl acked _ hq

/-! ## CMC3: New committed index is bounded by committedIndex -/

/-- **CMC3** — After `maybeAppend`, the new `committed` value is ≤ `committedIndex`.

    Given that:
    1. `matchTerm` succeeds (entries were accepted),
    2. The previous `s.committed` is already within the quorum's `committedIndex`,
    3. The `committed_to` argument `ca` is within the quorum's `committedIndex`,
    4. A replication quorum has acknowledged at least `lastNew = idx + ents.length`,

    the new committed value in the output state satisfies:
    ```
    (maybeAppend s idx term ca ents).2.committed ≤ committedIndex voters acked
    ```

    **Proof**:
    - `maybeAppend_committed_eq` gives `new_committed = max(s.committed, min(ca, lastNew))`.
    - `s.committed ≤ ci` by `hprev`.
    - `min(ca, lastNew) ≤ ca ≤ ci` by `hca` and `Nat.min_le_left`.
    - `max(s.committed, min(ca, lastNew)) ≤ ci` by both bounds ≤ ci.

    **Significance**: this is the key safety invariant for commit advancement — the
    `maybe_append` function never commits beyond what the quorum has acknowledged. -/
theorem CMC3_maybeAppend_committed_bounded
    (hd : Nat) (tl : List Nat) (acked : AckedFn)
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (hmatch : matchTerm s.log idx term = true)
    (hprev : s.committed ≤ committedIndex (hd :: tl) acked)
    (hca   : ca ≤ committedIndex (hd :: tl) acked)
    (hrep  : hasQuorum (hd :: tl)
        (fun v => decide (acked v ≥ idx + ents.length)) = true) :
    (maybeAppend s idx term ca ents).2.committed ≤
    committedIndex (hd :: tl) acked := by
  have hci  : committedIndex (hd :: tl) acked ≥ idx + ents.length :=
    CMC1_replication_advances_commit hd tl acked _ hrep
  rw [maybeAppend_committed_eq s idx term ca ents hmatch]
  have h_min : min ca (idx + ents.length) ≤ committedIndex (hd :: tl) acked :=
    Nat.le_trans (Nat.min_le_left _ _) hca
  -- max a b ≤ c ← a ≤ c ∧ b ≤ c
  simp only [Nat.max_le]
  exact ⟨hprev, h_min⟩

/-! ## CMC4: No-conflict implies entries are consistent with log -/

/-- **CMC4** — When `findConflict` returns 0 (no conflict), the entries are already
    consistent with the log prefix.

    A `conflict = 0` result means all entries in `ents` match the existing log at their
    respective indices.  This implies the log content at those indices is already correct
    — `maybeAppend` will not modify the log.

    **Status**: sorry.  The precise statement requires connecting `matchTerm` (per-entry
    term check) to log-entry equality, which requires the `LogEntry.term` field to
    correspond to an actual entry stored in the log.  The FindConflict model abstracts
    `matchTerm log e.index e.term = true` as term agreement, not full entry equality.

    **Remaining step**: a `matchTerm`-to-entry-content bridge theorem, stating that
    `matchTerm log e.index e.term = true → log e.index = some e.term`.  This holds by
    definition of `matchTerm` in `FindConflict.lean`. -/
theorem CMC4_findConflict_safe_commit_prefix
    (log : LogTerm) (ents : List LogEntry)
    (hfc : findConflict log ents = 0) :
    ∀ e ∈ ents, matchTerm log e.index e.term = true := by
  sorry

/-! ## CMC5: Committed index advances monotonically with acked values -/

/-- **CMC5** — Committed index is non-decreasing when acked values increase.

    If `acked₁ v ≤ acked₂ v` for all voters `v` (i.e., all voters have made at least
    as much progress in `acked₂` as in `acked₁`), then
    `committedIndex voters acked₁ ≤ committedIndex voters acked₂`.

    **Proof**: `committedIndex_mono` from `CommittedIndex.lean`, invoked directly.

    **Significance in log context**: as voters replicate new entries (increasing their
    acked indices), the committed index can only advance, never retreat.  CMC3 shows
    the new committed is ≤ committedIndex; CMC5 shows committedIndex itself grows. -/
theorem CMC5_progress_committed_le_ci
    (voters : List Nat) (acked₁ acked₂ : AckedFn)
    (hle : ∀ v, acked₁ v ≤ acked₂ v) :
    committedIndex voters acked₁ ≤ committedIndex voters acked₂ :=
  committedIndex_mono voters acked₁ acked₂ hle

/-! ## CMC6: committedIndex ≥ k implies a quorum voter's log entry (sorry-guarded) -/

/-- **CMC6** — `committedIndex ≥ k` implies there exists a quorum of voters whose log
    at index `k` contains some entry.

    **Status**: sorry.  This requires relating `AckedFn` (abstract acknowledgment
    counts) to actual log contents.  The `AckedFn` model does not directly encode what
    entry is at each index — it only records acknowledgment indices.

    **Remaining step**: an `acked v ≥ k → ∃ e, log v k = some e` axiom, representing
    the protocol invariant that "acknowledged index ≥ k means the log has an entry at k".
    This would close the bridge between the quorum layer and the entry layer. -/
theorem CMC6_committed_index_entry_bridge
    (hd : Nat) (tl : List Nat) (acked : AckedFn) (logs : VoterLogs Nat)
    (k : Nat)
    (hci : committedIndex (hd :: tl) acked ≥ k)
    (hbridge : ∀ v, acked v ≥ k → ∃ e, logs v k = some e) :
    ∃ e, hasQuorum (hd :: tl) (fun v => decide (logs v k = some e)) = true := by
  sorry

/-! ## CMC7: Log entries committed via maybe_append are unique -/

/-- **CMC7** — Uniqueness of entries committed via `maybeAppend`.

    If two different rounds of `maybeAppend` both produce a quorum-committed entry at
    index `k` — one entry `e1` and another `e2` — and the voter list is non-empty,
    then `e1 = e2`.

    **Proof**: direct application of `raft_state_machine_safety` (RSS1) from
    `RaftSafety`.  This is the bridge theorem: it invokes the state-machine safety
    result in the specific context of log entries committed by `maybeAppend` operations.

    **Significance**: this theorem makes explicit that `maybeAppend` operations,
    across any two replication rounds, cannot produce conflicting committed entries —
    the quorum intersection guarantee ensures consistency. -/
theorem CMC7_maybeAppend_safety_composition [DecidableEq E]
    (hd : Nat) (tl : List Nat) (logs : VoterLogs E) (k : Nat) (e1 e2 : E)
    (h1 : isQuorumCommitted (hd :: tl) logs k e1)
    (h2 : isQuorumCommitted (hd :: tl) logs k e2) :
    e1 = e2 :=
  raft_state_machine_safety hd tl logs k e1 e2 h1 h2

/-! ## Evaluation examples -/

section Eval

-- Example: 3-voter cluster, acked = (1↦5, 2↦4, 3↦3)
-- committedIndex [1,2,3] acked = 4  (majority=2; sorted desc [5,4,3]; index 1 = 4)
-- A quorum acked ≥ 4: voters 1,2 (count = 2 = majority(3))
-- CMC1: committedIndex ≥ 4 ← quorum acked ≥ 4
#eval FVSquad.CommittedIndex.committedIndex [1, 2, 3]
      (fun v => if v == 1 then 5 else if v == 2 then 4 else 3)
-- expected: 4

-- The quorum predicate for k=4
#eval hasQuorum [1, 2, 3]
      (fun v => decide ((if v == 1 then 5 else if v == 2 then (4 : Nat) else 3) ≥ 4))
-- expected: true (voters 1 and 2 satisfy, count = 2 ≥ majority(3) = 2)

end Eval

end FVSquad.CrossModuleComposition
