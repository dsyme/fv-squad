/-!
# MaybeAppend — Lean 4 Specification and Implementation Model

Formal specification of `RaftLog::maybe_append` and `RaftLog::maybe_commit`
from `raft-rs` (`src/raft_log.rs`).

## Model scope and approximations

* **Types**: All indices and terms are `Nat` (Rust uses `u64`; overflow not modelled).
* **Log abstraction**: The log is modelled as `logTerm : Nat → Option Nat`, a partial
  function from index to term. `none` models a compacted or nonexistent entry.
* **State**: `RaftState` carries `committed`, `persisted`, `lastIndex`, and `logTerm`.
* **Entry list**: represented as `List (Nat × Nat)` (index, term) pairs.
* **Omitted**: I/O, logging, panic semantics (modelled as preconditions),
  `max_apply_unpersisted_log_limit`, `applied`, snapshot interaction, `u64` overflow.
* **find_conflict**: modelled as functional scan on a `List`.
* **commitTo**: directly modelled; never decreases `committed`.

🔬 *Lean Squad — auto-generated formal specification.*

-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace FVSquad.MaybeAppend

/-! ## State Model -/

/-- Abstract Raft log state relevant to `maybe_append` and `maybe_commit`.

    Fields:
    * `committed`  — highest index known to be durably committed on a quorum
    * `persisted`  — highest index durably persisted locally
    * `lastIndex`  — highest index in the log
    * `logTerm`    — partial mapping from index to term (`none` = compacted/absent)

    Invariant (not enforced by the type): `committed ≤ lastIndex`. -/
structure RaftState where
  committed  : Nat
  persisted  : Nat
  lastIndex  : Nat
  logTerm    : Nat → Option Nat

/-! ## `matchTerm` -/

/-- `matchTerm s idx term` iff the entry at `idx` has term `term`. -/
def matchTerm (s : RaftState) (idx term : Nat) : Bool :=
  s.logTerm idx == some term

/-! ## `commitTo` -/

/-- `commitTo s toCommit` advances `committed` to `toCommit` (never decreases). -/
def commitTo (s : RaftState) (toCommit : Nat) : RaftState :=
  if s.committed >= toCommit then s
  else { s with committed := toCommit }

theorem commitTo_monotone (s : RaftState) (k : Nat) :
    (commitTo s k).committed ≥ s.committed := by
  simp [commitTo]
  split_ifs with h
  · exact h
  · omega

theorem commitTo_exact_or_unchanged (s : RaftState) (k : Nat) :
    (commitTo s k).committed = k ∨ (commitTo s k).committed = s.committed := by
  simp [commitTo]
  split_ifs with h
  · right; rfl
  · left; rfl

theorem commitTo_ge (s : RaftState) (k : Nat) :
    (commitTo s k).committed ≥ k ∨ (commitTo s k).committed = s.committed := by
  simp [commitTo]
  split_ifs with h
  · right; rfl
  · left; rfl

theorem commitTo_idempotent (s : RaftState) (k : Nat) :
    commitTo (commitTo s k) k = commitTo s k := by
  simp [commitTo]
  split_ifs with h1 h2
  · rfl
  · omega
  · rfl
  · rfl

/-! ## `findConflict` -/

/-- `findConflict s ents` returns the index of the first entry in `ents` whose term
    does not match the stored log, or 0 if all entries match (or `ents` is empty).

    Models `RaftLog::find_conflict`. -/
def findConflict (s : RaftState) (ents : List (Nat × Nat)) : Nat :=
  match ents with
  | [] => 0
  | (idx, term) :: rest =>
    if !matchTerm s idx term then idx
    else findConflict s rest

/-- `findConflict` returns 0 on an empty list. -/
@[simp]
theorem findConflict_nil (s : RaftState) : findConflict s [] = 0 := rfl

/-- If `findConflict` returns a non-zero index, the entry at that index does not match. -/
theorem findConflict_nonzero_no_match
    (s : RaftState) (ents : List (Nat × Nat))
    (h : findConflict s ents ≠ 0) :
    ∃ t : Nat, (findConflict s ents, t) ∈ ents ∧ !matchTerm s (findConflict s ents) t := by
  induction ents with
  | nil => simp at h
  | cons hd tl ih =>
    simp [findConflict] at h ⊢
    split_ifs with hm
    · -- term does not match head
      exact ⟨hd.2, Or.inl (by simp), hm⟩
    · -- head matched, recurse
      simp at hm
      obtain ⟨t, ht_mem, ht_mismatch⟩ := ih (by
        intro heq
        simp [findConflict, hm] at h)
      exact ⟨t, Or.inr ht_mem, ht_mismatch⟩

/-- If `findConflict` returns 0, every entry matches the log.

    Requires that all entry indices are nonzero (`hpos`), which holds in Raft because
    log indices start at 1 (index 0 is a sentinel for "no entry"). Without this
    precondition the sentinel value 0 is ambiguous: `findConflict` returns 0 both for
    "no conflict found" and "conflict at index 0". -/
theorem findConflict_zero_all_match
    (s : RaftState) (ents : List (Nat × Nat))
    (hpos : ∀ e ∈ ents, e.1 ≠ 0)
    (h : findConflict s ents = 0) :
    ∀ idx term, (idx, term) ∈ ents → matchTerm s idx term = true := by
  induction ents with
  | nil => intros; simp_all
  | cons hd tl ih =>
    simp [findConflict] at h
    split_ifs with hm at h
    · -- hm : !matchTerm s hd.1 hd.2 = true, so findConflict returned hd.1
      -- h : hd.1 = 0, but hpos says hd.1 ≠ 0 — contradiction
      exact absurd h (hpos hd (List.mem_cons_self _ _))
    · simp at hm
      intro idx term hmem
      simp at hmem
      rcases hmem with rfl | hmem
      · exact hm
      · exact ih (fun e he => hpos e (List.mem_cons_of_mem _ he)) h idx term hmem

/-- `findConflict` result is either 0 or is the index of some entry in `ents`. -/
theorem findConflict_mem_or_zero
    (s : RaftState) (ents : List (Nat × Nat)) :
    findConflict s ents = 0 ∨ ∃ t, (findConflict s ents, t) ∈ ents := by
  induction ents with
  | nil => left; rfl
  | cons hd tl ih =>
    simp [findConflict]
    split_ifs with hm
    · right; exact ⟨hd.2, List.mem_cons_self _ _⟩
    · rcases ih with h | ⟨t, ht⟩
      · left; exact h
      · right; exact ⟨t, List.mem_cons_of_mem _ ht⟩

/-! ## `maybeCommit` -/

/-- Result of `maybeCommit`. -/
structure CommitResult where
  newState : RaftState
  advanced : Bool

/-- `maybeCommit s maxIndex term` commits `maxIndex` if it exceeds `committed` and
    the entry has the given `term`.

    Models `RaftLog::maybe_commit`. -/
def maybeCommit (s : RaftState) (maxIndex term : Nat) : CommitResult :=
  if maxIndex > s.committed && s.logTerm maxIndex == some term then
    ⟨commitTo s maxIndex, true⟩
  else
    ⟨s, false⟩

theorem maybeCommit_monotone (s : RaftState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).newState.committed ≥ s.committed := by
  simp [maybeCommit]
  split_ifs with h
  · exact commitTo_monotone s maxIndex
  · rfl

theorem maybeCommit_true_iff (s : RaftState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).advanced = true ↔
    maxIndex > s.committed ∧ s.logTerm maxIndex = some term := by
  simp [maybeCommit]
  split_ifs with h
  · simp [Bool.and_eq_true_iff] at h
    obtain ⟨hgt, hterm⟩ := h
    exact ⟨fun _ => ⟨Nat.lt_of_lt_of_le (by omega) (le_refl _), by
        simp [beq_eq_true_iff] at hterm; exact hterm⟩,
      fun _ => rfl⟩
  · simp; intro hgt hterm
    simp [Bool.and_eq_false_iff] at h
    rcases h with h | h
    · simp [Bool.not_eq_true] at h; omega
    · simp [beq_eq_false_iff_ne] at h; exact absurd hterm h

theorem maybeCommit_false_unchanged (s : RaftState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).advanced = false →
    (maybeCommit s maxIndex term).newState = s := by
  simp [maybeCommit]
  split_ifs with h
  · intro hf; simp at hf
  · intro; rfl

theorem maybeCommit_true_committed (s : RaftState) (maxIndex term : Nat) :
    (maybeCommit s maxIndex term).advanced = true →
    (maybeCommit s maxIndex term).newState.committed = maxIndex := by
  simp [maybeCommit, commitTo]
  split_ifs with h1 h2
  · intro; rfl
  · intro; rfl
  · intro hf; simp at hf

/-! ## `maybeAppend` -/

/-- Result of `maybeAppend`. -/
structure AppendResult where
  newState    : RaftState
  conflictIdx : Nat   -- 0 = no conflict
  lastNewIdx  : Nat
  matched     : Bool  -- false = term mismatch, no change

/-- `applyEntries s conflictIdx baseIdx ents` appends the suffix of `ents` starting
    at `conflictIdx`, and lowers `persisted` to `conflictIdx - 1` if needed.

    This models the append + persisted-reset step inside `maybe_append`. -/
def applyEntries (s : RaftState) (conflictIdx baseIdx : Nat)
    (ents : List (Nat × Nat)) : RaftState :=
  let newLogTerm : Nat → Option Nat := fun i =>
    -- Entries from conflictIdx onward in `ents` overwrite the log
    let pos := (i : Int) - (baseIdx : Int) - 1
    if pos ≥ 0 && (pos.toNat) < ents.length && i ≥ conflictIdx then
      some (ents.get ⟨pos.toNat, by omega⟩).2
    else
      s.logTerm i
  let newPersisted :=
    if s.persisted > conflictIdx - 1 then conflictIdx - 1 else s.persisted
  let newLastIndex := baseIdx + ents.length
  { s with
    logTerm   := newLogTerm
    persisted := newPersisted
    lastIndex := max s.lastIndex newLastIndex }

/-- `maybeAppend s idx term committed ents` models `RaftLog::maybe_append`.

    Precondition (not encoded in the type):
    * If `findConflict s ents ≠ 0` then `findConflict s ents > s.committed`
      (panic otherwise; this precondition captures non-panicking executions).

    Returns an `AppendResult`. -/
def maybeAppend (s : RaftState) (idx term committed : Nat)
    (ents : List (Nat × Nat)) : AppendResult :=
  if matchTerm s idx term then
    let conflictIdx := findConflict s ents
    let lastNewIdx  := idx + ents.length
    -- Apply entries if there's a conflict (conflictIdx > 0)
    let s' := if conflictIdx == 0 then s else applyEntries s conflictIdx idx ents
    -- Advance commit to min(committed, lastNewIdx)
    let newCommitted := min committed lastNewIdx
    let s'' := commitTo s' newCommitted
    ⟨s'', conflictIdx, lastNewIdx, true⟩
  else
    ⟨s, 0, 0, false⟩

/-! ## Key theorems about `maybeAppend` -/

/-- `maybeAppend` returns `matched = false` iff the term does not match. -/
theorem maybeAppend_no_match (s : RaftState) (idx term committed : Nat)
    (ents : List (Nat × Nat)) :
    (maybeAppend s idx term committed ents).matched = false ↔
    ¬matchTerm s idx term := by
  simp [maybeAppend]
  split_ifs with h
  · simp
  · simp [Bool.not_eq_true] at h ⊢; exact h

/-- If no match, the state is unchanged. -/
theorem maybeAppend_no_match_state (s : RaftState) (idx term committed : Nat)
    (ents : List (Nat × Nat)) (h : ¬matchTerm s idx term) :
    (maybeAppend s idx term committed ents).newState = s := by
  simp [maybeAppend, Bool.not_eq_true.mp h]

/-- Commit index never decreases after `maybeAppend`. -/
theorem maybeAppend_committed_monotone (s : RaftState) (idx term committed : Nat)
    (ents : List (Nat × Nat)) :
    (maybeAppend s idx term committed ents).newState.committed ≥ s.committed := by
  simp [maybeAppend]
  split_ifs with h
  · -- matched branch: commit = commitTo(s', min(committed, lastNew))
    apply le_trans
    · exact le_refl _
    · -- commitTo is monotone
      apply le_trans (commitTo_monotone _ _)
      -- s'.committed = s.committed (applyEntries doesn't change committed)
      simp [applyEntries, commitTo]
      split_ifs <;> simp [applyEntries]
  · rfl

/-- If `maybeAppend` returns matched, the new commit is bounded by the leader's commit.

    Requires `hle : s.committed ≤ committed` — a protocol invariant: a follower cannot
    already be committed beyond a valid leader message. -/
theorem maybeAppend_commit_le_leader (s : RaftState) (idx term committed : Nat)
    (ents : List (Nat × Nat)) (hm : matchTerm s idx term)
    (hle : s.committed ≤ committed) :
    (maybeAppend s idx term committed ents).newState.committed ≤ committed := by
  simp [maybeAppend, hm]
  -- goal: (commitTo (if findConflict s ents == 0 then s else applyEntries ...) (min committed (idx+ents.length))).committed ≤ committed
  have hap : (applyEntries s (findConflict s ents) idx ents).committed = s.committed := by
    simp [applyEntries]
  split_ifs with hc
  · -- no-conflict branch: s' = s
    rcases commitTo_exact_or_unchanged s (min committed (idx + ents.length)) with h | h
    · rw [h]; exact Nat.min_le_left _ _
    · rw [h]; exact hle
  · -- conflict branch: s' = applyEntries ...
    rcases commitTo_exact_or_unchanged (applyEntries s (findConflict s ents) idx ents)
        (min committed (idx + ents.length)) with h | h
    · rw [h]; exact Nat.min_le_left _ _
    · rw [h, hap]; exact hle

/-- If `maybeAppend` returns matched, the new commit is bounded by `lastNewIdx`.

    Requires `hle : s.committed ≤ idx + ents.length` — entries must span at least as
    far as the follower's current commit, which holds for any valid append message. -/
theorem maybeAppend_commit_le_lastNew (s : RaftState) (idx term committed : Nat)
    (ents : List (Nat × Nat)) (hm : matchTerm s idx term)
    (hle : s.committed ≤ idx + ents.length) :
    (maybeAppend s idx term committed ents).newState.committed ≤
    (maybeAppend s idx term committed ents).lastNewIdx := by
  simp [maybeAppend, hm]
  -- goal: (commitTo (if ...) (min committed (idx+ents.length))).committed ≤ idx+ents.length
  have hap : (applyEntries s (findConflict s ents) idx ents).committed = s.committed := by
    simp [applyEntries]
  split_ifs with hc
  · -- no-conflict branch: s' = s
    rcases commitTo_exact_or_unchanged s (min committed (idx + ents.length)) with h | h
    · rw [h]; exact Nat.min_le_right _ _
    · rw [h]; exact hle
  · -- conflict branch: s' = applyEntries ...
    rcases commitTo_exact_or_unchanged (applyEntries s (findConflict s ents) idx ents)
        (min committed (idx + ents.length)) with h | h
    · rw [h]; exact Nat.min_le_right _ _
    · rw [h, hap]; exact hle

/-- The `lastNewIdx` returned equals `idx + ents.length` when matched. -/
theorem maybeAppend_lastNewIdx (s : RaftState) (idx term committed : Nat)
    (ents : List (Nat × Nat)) (hm : matchTerm s idx term) :
    (maybeAppend s idx term committed ents).lastNewIdx = idx + ents.length := by
  simp [maybeAppend, hm]

/-- No-truncation safety: the precondition that prevents panic.
    If there IS a conflict and `conflictIdx > 0`, then `conflictIdx > committed`
    (in non-panicking executions). This is a property of the CALLER, not of
    `maybe_append` itself; we state it as an assumption available to callers. -/
theorem maybeAppend_conflict_gt_committed
    (s : RaftState) (idx term committed : Nat)
    (ents : List (Nat × Nat)) (hm : matchTerm s idx term)
    -- Safety precondition: no conflict at or below committed
    (hpre : findConflict s ents ≠ 0 → findConflict s ents > s.committed) :
    let r := maybeAppend s idx term committed ents
    r.conflictIdx = 0 ∨ r.conflictIdx > s.committed := by
  simp [maybeAppend, hm]
  by_cases h : findConflict s ents = 0
  · left; exact h
  · right; exact hpre h

/-! ## Sanity checks -/

-- matchTerm on a known log
#eval
  let s : RaftState := {
    committed := 1, persisted := 3, lastIndex := 3,
    logTerm := fun i => if i == 1 then some 1 else if i == 2 then some 2 else
                        if i == 3 then some 3 else none
  }
  matchTerm s 2 2  -- true

-- maybeCommit: advancing commit when term matches
#eval
  let s : RaftState := {
    committed := 2, persisted := 4, lastIndex := 4,
    logTerm := fun i => if i == 3 then some 2 else if i == 4 then some 2 else none
  }
  let r := maybeCommit s 3 2
  (r.advanced, r.newState.committed)  -- (true, 3)

-- maybeCommit: no advance when term mismatches
#eval
  let s : RaftState := {
    committed := 2, persisted := 4, lastIndex := 4,
    logTerm := fun i => if i == 3 then some 2 else none
  }
  let r := maybeCommit s 3 1
  (r.advanced, r.newState.committed)  -- (false, 2)

-- findConflict: empty entries → 0
#eval
  let s : RaftState := { committed := 0, persisted := 0, lastIndex := 0,
    logTerm := fun _ => none }
  findConflict s []  -- 0

-- maybeAppend: no match returns unchanged
#eval
  let s : RaftState := {
    committed := 1, persisted := 3, lastIndex := 3,
    logTerm := fun i => if i == 3 then some 3 else none
  }
  let r := maybeAppend s 3 99 3 []
  (r.matched, r.newState.committed)  -- (false, 1)

end FVSquad.MaybeAppend
