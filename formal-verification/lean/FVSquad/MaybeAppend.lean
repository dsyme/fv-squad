import FVSquad.FindConflict

/-!
# MaybeAppend — Lean 4 Specification and Implementation Model

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Formal specification and implementation model of `RaftLog::maybe_append`
from `src/raft_log.rs` (lines 267–298).

## Algorithm (Rust)

```rust
pub fn maybe_append(&mut self, idx: u64, term: u64, committed: u64, ents: &[Entry])
    -> Option<(u64, u64)>
{
    if self.match_term(idx, term) {
        let conflict_idx = self.find_conflict(ents);
        if conflict_idx == 0 {
            // no conflict
        } else if conflict_idx <= self.committed {
            fatal!(...) // panic — safety violation (not modelled)
        } else {
            let start = (conflict_idx - (idx + 1)) as usize;
            self.append(&ents[start..]);
            if self.persisted > conflict_idx - 1 {
                self.persisted = conflict_idx - 1;
            }
        }
        let last_new_index = idx + ents.len() as u64;
        self.commit_to(cmp::min(committed, last_new_index));
        return Some((conflict_idx, last_new_index));
    }
    None
}
```

## Model scope and approximations

* **State**: `{ log : LogTerm, committed : Nat, persisted : Nat }`.
* **Abstract log**: `Nat → Option Nat` (index → optional term). Stable/unstable
  storage split abstracted away.
* **Types**: `Nat` for `u64`. No overflow, no `u64::MAX` sentinel.
* **Consecutive entries**: Theorems about log contents assume consecutive indexing
  (`ents[k].index = idx + 1 + k`), stated as explicit preconditions where needed.
* **Panics omitted**: `conflict ≤ committed` panic is not modelled.
* **Omitted**: logging, concurrency, payload fields, `Err`/`Ok` term variants.

## Task coverage

* **Task 3** (Formal Spec Writing): Types, function model, and correctness
  theorems MA1–MA13 covering return value, committed bounds, persisted rollback,
  and log prefix preservation.
* **Task 4** (Implementation Extraction): Helper functions `logWithEntries` and
  `applyConflict`, and theorems MA14–MA16 connecting the implementation model
  to log-content properties.
-/

namespace FVSquad.MaybeAppend

open FVSquad.FindConflict

/-! ## State model -/

/-- Abstract Raft log state for `maybe_append` modelling. -/
structure RaftState where
  log       : LogTerm
  committed : Nat
  persisted : Nat

/-! ## Helper: update log with entries -/

/-- Write a list of log entries into an abstract log (first occurrence per index wins).
    Corresponds to `self.append(suffix)` in the Rust implementation. -/
def logWithEntries (log : LogTerm) (entries : List LogEntry) (i : Nat) : Option Nat :=
  match entries with
  | []        => log i
  | e :: rest =>
    if i = e.index then some e.term
    else logWithEntries log rest i

/-! ## Implementation model -/

/-- Apply a conflict: if `conflict > 0`, overwrite the log starting at
    `ents.drop (conflict - (idx + 1))` (the suffix after the conflict point).
    Corresponds to the `else` branch in `maybe_append` that calls `self.append`. -/
def applyConflict (log : LogTerm) (conflict idx : Nat) (ents : List LogEntry) : LogTerm :=
  if conflict = 0 then log
  else logWithEntries log (ents.drop (conflict - (idx + 1)))

/-- Pure functional model of `RaftLog::maybe_append`.

    Returns `(result, new_state)`:
    - `result = None` if `match_term(idx, term)` fails (wrong leader claim).
    - `result = Some (conflict_idx, last_new_idx)` on success.

    State updates on success:
    - **log**: truncated at `conflict` and new suffix appended (via `applyConflict`).
    - **committed**: advanced to `max(s.committed, min(ca, last_new_idx))`.
    - **persisted**: reset to `conflict - 1` if `persisted ≥ conflict > 0`.

    **Model approximation**: the `conflict ≤ committed` panic is not modelled; callers
    are assumed to satisfy `conflict > committed ∨ conflict = 0`. -/
def maybeAppend (s : RaftState) (idx term ca : Nat) (ents : List LogEntry) :
    Option (Nat × Nat) × RaftState :=
  match matchTerm s.log idx term with
  | false => (none, s)
  | true  =>
    let conflict     := findConflict s.log ents
    let lastNew      := idx + ents.length
    let newLog       := applyConflict s.log conflict idx ents
    let newPersisted :=
      if conflict = 0 then s.persisted
      else if s.persisted ≥ conflict then conflict - 1
      else s.persisted
    let newCommitted := max s.committed (min ca lastNew)
    (some (conflict, lastNew),
     { log := newLog, committed := newCommitted, persisted := newPersisted })

/-! ## Return-value theorems (MA1–MA4) -/

/-- MA1: Non-match → result is `None`. The log, committed, and persisted are unchanged. -/
theorem maybeAppend_none (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = false) :
    (maybeAppend s idx term ca ents) = (none, s) := by
  simp [maybeAppend, h]

/-- MA2: Match → result is `Some (conflict, lastNew)`.
    `conflict = findConflict s.log ents`,  `lastNew = idx + ents.length`. -/
theorem maybeAppend_some (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true) :
    (maybeAppend s idx term ca ents).1 =
      some (findConflict s.log ents, idx + ents.length) := by
  simp [maybeAppend, h]

/-- MA3: On success, first result component equals `findConflict`. -/
theorem maybeAppend_conflict_eq (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true) :
    ∃ lastNew, (maybeAppend s idx term ca ents).1 = some (findConflict s.log ents, lastNew) :=
  ⟨idx + ents.length, maybeAppend_some s idx term ca ents h⟩

/-- MA4: On success, second result component equals `idx + ents.length`. -/
theorem maybeAppend_lastNew_eq (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true) :
    ∃ conflict, (maybeAppend s idx term ca ents).1 = some (conflict, idx + ents.length) :=
  ⟨findConflict s.log ents, maybeAppend_some s idx term ca ents h⟩

/-! ## Committed index theorems (MA5–MA9) -/

/-- MA5: New committed = `max(s.committed, min(ca, idx + ents.length))`. -/
theorem maybeAppend_committed_eq (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true) :
    (maybeAppend s idx term ca ents).2.committed =
      max s.committed (min ca (idx + ents.length)) := by
  simp [maybeAppend, h]

/-- MA6: Committed never decreases. -/
theorem maybeAppend_committed_mono (s : RaftState) (idx term ca : Nat) (ents : List LogEntry) :
    s.committed ≤ (maybeAppend s idx term ca ents).2.committed := by
  cases hm : matchTerm s.log idx term
  · simp [maybeAppend, hm]
  · simp [maybeAppend, hm]
    exact Nat.le_max_left _ _

/-- MA7: Committed ≤ `ca` (when prior committed ≤ `ca`). -/
theorem maybeAppend_committed_le_ca (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hca : s.committed ≤ ca) :
    (maybeAppend s idx term ca ents).2.committed ≤ ca := by
  simp [maybeAppend, h]
  exact Nat.max_le.mpr ⟨hca, Nat.min_le_left _ _⟩

/-- MA8: Committed ≤ `lastNew` (when prior committed ≤ `lastNew`). -/
theorem maybeAppend_committed_le_lastNew
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hlast : s.committed ≤ idx + ents.length) :
    (maybeAppend s idx term ca ents).2.committed ≤ idx + ents.length := by
  simp [maybeAppend, h]
  exact Nat.max_le.mpr ⟨hlast, Nat.min_le_right _ _⟩

/-- MA9: Committed = `min(ca, lastNew)` when both `ca` and `lastNew` bound `s.committed`. -/
theorem maybeAppend_committed_eq_min
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hca   : s.committed ≤ ca)
    (hlast : s.committed ≤ idx + ents.length) :
    (maybeAppend s idx term ca ents).2.committed = min ca (idx + ents.length) := by
  simp [maybeAppend, h]
  by_cases hcl : ca ≤ idx + ents.length
  · rw [Nat.min_eq_left hcl]; exact Nat.max_eq_right hca
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.not_le.mp hcl))]; exact Nat.max_eq_right hlast

/-! ## Persisted index theorems (MA10–MA12) -/

/-- MA10: Persisted unchanged when there is no conflict. -/
theorem maybeAppend_persisted_no_conflict
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hzero : findConflict s.log ents = 0) :
    (maybeAppend s idx term ca ents).2.persisted = s.persisted := by
  simp [maybeAppend, h, hzero]

/-- MA11: Persisted rolled back to `conflict - 1` when `persisted ≥ conflict > 0`. -/
theorem maybeAppend_persisted_rollback
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hne : findConflict s.log ents ≠ 0)
    (hge : s.persisted ≥ findConflict s.log ents) :
    (maybeAppend s idx term ca ents).2.persisted = findConflict s.log ents - 1 := by
  simp [maybeAppend, h, hne, hge]

/-- MA12: Persisted unchanged when `persisted < conflict`. -/
theorem maybeAppend_persisted_preserved
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hne : findConflict s.log ents ≠ 0)
    (hlt : s.persisted < findConflict s.log ents) :
    (maybeAppend s idx term ca ents).2.persisted = s.persisted := by
  simp only [maybeAppend, h]
  have hnotge : ¬ (findConflict s.log ents ≤ s.persisted) := by omega
  rw [if_neg hne, if_neg hnotge]

/-! ## Log content theorems (MA13–MA16, Task 4) -/

/-- Helper (LWE1): `logWithEntries` does not modify indices absent from the entry list. -/
theorem logWithEntries_not_in
    (log : LogTerm) (entries : List LogEntry) (i : Nat)
    (h : ∀ e ∈ entries, e.index ≠ i) :
    logWithEntries log entries i = log i := by
  induction entries with
  | nil => simp [logWithEntries]
  | cons e rest ih =>
    show (if i = e.index then some e.term else logWithEntries log rest i) = log i
    have hne : ¬(i = e.index) := fun heq => h e List.mem_cons_self heq.symm
    rw [if_neg hne]
    exact ih (fun e' he' => h e' (List.mem_cons_of_mem e he'))

/-- MA13: Log entries before the conflict index are preserved.

    Precondition `hsuf`: every entry in the applied suffix has index ≥ `conflict`.
    This holds for consecutive entries: `ents[k].index = idx + 1 + k`. -/
theorem maybeAppend_log_prefix_preserved
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hc : findConflict s.log ents > 0)
    (hsuf : ∀ e ∈ ents.drop (findConflict s.log ents - (idx + 1)),
              findConflict s.log ents ≤ e.index)
    (i : Nat) (hi : i < findConflict s.log ents) :
    (maybeAppend s idx term ca ents).2.log i = s.log i := by
  have hne : findConflict s.log ents ≠ 0 := by omega
  simp only [maybeAppend, h, applyConflict, if_neg hne]
  apply logWithEntries_not_in
  intro e he hei
  have hge := hsuf e he
  omega

/-- Helper (LWE2): `logWithEntries` reflects the first occurrence of an entry's index.

    If `e` is in `pre ++ e :: suf` and no entry in `pre` has `e.index`, then
    `logWithEntries log (pre ++ e :: suf) e.index = some e.term`. -/
theorem logWithEntries_mem_first
    (log : LogTerm) (pre : List LogEntry) (e : LogEntry) (suf : List LogEntry)
    (huniq : ∀ e' ∈ pre, e'.index ≠ e.index) :
    logWithEntries log (pre ++ e :: suf) e.index = some e.term := by
  induction pre with
  | nil =>
    show (if e.index = e.index then some e.term else logWithEntries log suf e.index) = some e.term
    simp
  | cons h t ih =>
    show (if e.index = h.index then some h.term
          else logWithEntries log (t ++ e :: suf) e.index) = some e.term
    have hne : e.index ≠ h.index := fun heq => huniq h List.mem_cons_self heq.symm
    rw [if_neg hne]
    exact ih (fun e' he' => huniq e' (List.mem_cons_of_mem h he'))

/-- MA14: After a successful append with `conflict > 0`, entries in the applied suffix
    are reflected in the new log.

    For an entry `e` that is the first occurrence of its index in the suffix
    `ents.drop (conflict - (idx + 1))`, the new log has `some e.term` at `e.index`. -/
theorem maybeAppend_suffix_applied
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hc : findConflict s.log ents > 0)
    (pre : List LogEntry) (e : LogEntry) (suf : List LogEntry)
    (hsplit : ents.drop (findConflict s.log ents - (idx + 1)) = pre ++ e :: suf)
    (huniq : ∀ e' ∈ pre, e'.index ≠ e.index) :
    (maybeAppend s idx term ca ents).2.log e.index = some e.term := by
  have hne : findConflict s.log ents ≠ 0 := by omega
  simp only [maybeAppend, h, applyConflict, if_neg hne, hsplit]
  exact logWithEntries_mem_first s.log pre e suf huniq

/-- MA15: When there is no conflict, the log is unchanged. -/
theorem maybeAppend_log_no_conflict
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = true)
    (hzero : findConflict s.log ents = 0) :
    (maybeAppend s idx term ca ents).2.log = s.log := by
  simp [maybeAppend, h, applyConflict, hzero]

/-- MA16: On failure, the entire state is unchanged. -/
theorem maybeAppend_state_unchanged_on_failure
    (s : RaftState) (idx term ca : Nat) (ents : List LogEntry)
    (h : matchTerm s.log idx term = false) :
    (maybeAppend s idx term ca ents).2 = s := by
  simp [maybeAppend, h]

end FVSquad.MaybeAppend
