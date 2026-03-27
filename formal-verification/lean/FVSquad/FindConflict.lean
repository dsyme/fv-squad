/-!
# FindConflict — Lean 4 Specification and Implementation Model

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Formal specification and implementation model of `RaftLog::find_conflict` from
`src/raft_log.rs` (lines 195–216).

## Algorithm

Scan a slice of log entries linearly.  For each entry, ask whether the local log agrees
(same term at that index).  Return the index of the **first disagreeing entry**, or **0**
if every entry agrees.

```
find_conflict(ents):
  for e in ents:
    if !match_term(e.index, e.term): return e.index
  return 0
```

## Model scope and approximations

* **Abstract log**: modelled as `Nat → Option Nat` (index → optional term).
  The real `RaftLog` stores entries split across a stable store and an unstable buffer;
  this is abstracted away.
* **Types**: log indices and terms are `Nat` (Rust: `u64`).
* **Positive-index precondition**: Raft log indices start at 1.  Index 0 is the "no
  conflict" sentinel returned by `find_conflict`, so theorems that reason about the
  absence of conflict require `∀ e ∈ ents, 0 < e.index`.
* **Omitted**: logging/tracing side effects, `Err`/`Ok` variants of `term()` (abstracted
  into `Option`), group-commit, concurrency, unsafe Rust.
* **`match_term` semantics**: returns `false` for any index where the log has no entry
  (out of range), mirroring `term(idx).map(|t| t == term).unwrap_or(false)`.
-/

namespace FVSquad.FindConflict

/-! ## Types -/

/-- A log entry: the pair (index, term) sent in an AppendEntries RPC. -/
structure LogEntry where
  index : Nat
  term  : Nat
  deriving Repr, DecidableEq

/-- Abstract log: maps an index to its stored term, or `none` if out of range. -/
abbrev LogTerm := Nat → Option Nat

/-! ## Core functions -/

/-- Does the log have `term` at position `idx`?
    Mirrors `self.term(idx).map(|t| t == term).unwrap_or(false)`. -/
def matchTerm (log : LogTerm) (idx term : Nat) : Bool :=
  match log idx with
  | some t => t == term
  | none   => false

/-- Scan `ents` for the first entry whose term does not match the log.
    Returns the conflicting entry's index, or 0 if all entries are consistent. -/
def findConflict (log : LogTerm) (ents : List LogEntry) : Nat :=
  match ents with
  | []         => 0
  | e :: rest  =>
    if !matchTerm log e.index e.term then e.index
    else findConflict log rest

/-! ## Structural lemmas (follow directly from the definition) -/

/-- FC1: Empty list → no conflict. -/
theorem findConflict_empty (log : LogTerm) :
    findConflict log [] = 0 := rfl

/-- FC2: Head entry mismatches → return head index immediately. -/
theorem findConflict_head_mismatch (log : LogTerm) (e : LogEntry) (rest : List LogEntry)
    (h : matchTerm log e.index e.term = false) :
    findConflict log (e :: rest) = e.index := by
  simp [findConflict, h]

/-- FC3: Head entry matches → recurse into the tail. -/
theorem findConflict_head_match (log : LogTerm) (e : LogEntry) (rest : List LogEntry)
    (h : matchTerm log e.index e.term = true) :
    findConflict log (e :: rest) = findConflict log rest := by
  simp [findConflict, h]

/-! ## Key correctness properties -/

/-- FC4a: If every entry matches, the result is 0. -/
theorem findConflict_zero_of_all_match (log : LogTerm) (ents : List LogEntry)
    (hall : ∀ e ∈ ents, matchTerm log e.index e.term = true) :
    findConflict log ents = 0 := by
  induction ents with
  | nil => rfl
  | cons e rest ih =>
    have he : matchTerm log e.index e.term = true :=
      hall e List.mem_cons_self
    rw [findConflict_head_match log e rest he]
    exact ih (fun e' he' => hall e' (List.mem_cons_of_mem e he'))

/-- FC4b: If the result is 0 and all indices are positive, every entry matches.
    (The positive-index precondition distinguishes the "no conflict" sentinel from
    a genuine index-0 entry, which does not exist in practice.) -/
theorem findConflict_all_match_of_zero (log : LogTerm) (ents : List LogEntry)
    (hzero : findConflict log ents = 0)
    (hpos  : ∀ e ∈ ents, 0 < e.index) :
    ∀ e ∈ ents, matchTerm log e.index e.term = true := by
  induction ents with
  | nil => intro e he; simp at he
  | cons e rest ih =>
    intro e' he'
    -- Case-split on whether the head matches.
    cases hm : matchTerm log e.index e.term with
    | true =>
      rw [findConflict_head_match log e rest hm] at hzero
      cases List.mem_cons.mp he' with
      | inl heq =>
        rw [heq]; exact hm
      | inr hrest =>
        exact ih hzero (fun e'' he'' => hpos e'' (List.mem_cons_of_mem e he'')) e' hrest
    | false =>
      -- findConflict = e.index, but hzero says the result is 0; e.index > 0: contradiction.
      rw [findConflict_head_mismatch log e rest hm] at hzero
      have : 0 < e.index := hpos e List.mem_cons_self
      omega

/-- FC5+FC6: If the result is non-zero, there is a witnessing entry:
    its index equals the result, and it mismatches the log. -/
theorem findConflict_nonzero_witness (log : LogTerm) (ents : List LogEntry)
    (hne : findConflict log ents ≠ 0) :
    ∃ e ∈ ents, e.index = findConflict log ents ∧ matchTerm log e.index e.term = false := by
  induction ents with
  | nil => simp [findConflict] at hne
  | cons e rest ih =>
    cases hm : matchTerm log e.index e.term with
    | false =>
      rw [findConflict_head_mismatch log e rest hm]
      exact ⟨e, List.mem_cons_self, rfl, hm⟩
    | true =>
      rw [findConflict_head_match log e rest hm] at hne ⊢
      obtain ⟨e', he', heq, hmm⟩ := ih hne
      exact ⟨e', List.mem_cons_of_mem e he', heq, hmm⟩

/-- FC7: First-mismatch characterisation.
    If all entries in `pre` match and entry `e` mismatches, then `findConflict` on
    `pre ++ e :: suf` returns `e.index`.  This characterises exactly *which* entry's
    index is returned: the first one that doesn't match. -/
theorem findConflict_first_mismatch
    (log  : LogTerm)
    (pre  : List LogEntry) (e : LogEntry) (suf : List LogEntry)
    (hpre : ∀ e' ∈ pre, matchTerm log e'.index e'.term = true)
    (he   : matchTerm log e.index e.term = false) :
    findConflict log (pre ++ e :: suf) = e.index := by
  induction pre with
  | nil =>
    simp only [List.nil_append]
    exact findConflict_head_mismatch log e suf he
  | cons h t ih =>
    have hh : matchTerm log h.index h.term = true :=
      hpre h List.mem_cons_self
    simp only [List.cons_append]
    rw [findConflict_head_match log h (t ++ e :: suf) hh]
    exact ih (fun e' he' => hpre e' (List.mem_cons_of_mem h he'))

/-- FC8: A matching prefix is transparent — it does not affect the result. -/
theorem findConflict_skip_match_prefix
    (log : LogTerm)
    (pre suf : List LogEntry)
    (hpre : ∀ e ∈ pre, matchTerm log e.index e.term = true) :
    findConflict log (pre ++ suf) = findConflict log suf := by
  induction pre with
  | nil => simp
  | cons h t ih =>
    have hh : matchTerm log h.index h.term = true :=
      hpre h List.mem_cons_self
    simp only [List.cons_append]
    rw [findConflict_head_match log h (t ++ suf) hh]
    exact ih (fun e' he' => hpre e' (List.mem_cons_of_mem h he'))

/-! ## Combined / corollary theorems -/

/-- FC9: Singleton matching entry → 0. -/
theorem findConflict_singleton_match (log : LogTerm) (e : LogEntry)
    (h : matchTerm log e.index e.term = true) :
    findConflict log [e] = 0 := by
  simp [findConflict, h]

/-- FC10: Singleton mismatching entry → e.index. -/
theorem findConflict_singleton_mismatch (log : LogTerm) (e : LogEntry)
    (h : matchTerm log e.index e.term = false) :
    findConflict log [e] = e.index := by
  simp [findConflict, h]

/-- FC11: Result is 0 iff all entries match (for positive-index entries).
    Combines FC4a and FC4b into a biconditional. -/
theorem findConflict_zero_iff_all_match
    (log  : LogTerm)
    (ents : List LogEntry)
    (hpos : ∀ e ∈ ents, 0 < e.index) :
    findConflict log ents = 0 ↔ ∀ e ∈ ents, matchTerm log e.index e.term = true :=
  ⟨fun h  => findConflict_all_match_of_zero log ents h hpos,
   fun h  => findConflict_zero_of_all_match log ents h⟩

/-- FC12: The result, if non-zero, is a member of `{e.index | e ∈ ents}`.
    (Follows immediately from FC5+FC6.) -/
theorem findConflict_result_in_indices (log : LogTerm) (ents : List LogEntry)
    (hne : findConflict log ents ≠ 0) :
    ∃ e ∈ ents, e.index = findConflict log ents :=
  let ⟨e, hmem, heq, _⟩ := findConflict_nonzero_witness log ents hne
  ⟨e, hmem, heq⟩

end FVSquad.FindConflict
