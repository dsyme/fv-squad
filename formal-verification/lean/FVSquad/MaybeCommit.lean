import FVSquad.FindConflict

/-!
# MaybeCommit — Model and Proofs for `RaftLog::maybe_commit`

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides a formal model of `RaftLog::maybe_commit` (`src/raft_log.rs:530`) and
`RaftLog::commit_to` (`src/raft_log.rs:304`), and proves their key correctness properties.

The central result is the **A6 term safety condition** (Raft §5.4.2): a Raft leader only
advances `committed` when the entry at the target index was written in the leader's **current
term**.  This prevents the "figure 8" problem where stale entries from an old leader could be
committed in a later term, violating the safety invariant.

## Background

In Raft (§5.4.2), a leader may only directly commit entries from its **current term**.  Entries
from previous terms are committed *indirectly* — they become committed when the leader appends
at least one entry from its current term that follows them.

`RaftLog::maybe_commit` enforces this with a term check:
```rust
if max_index > self.committed &&
   self.zero_term_on_err_compacted(self.term(max_index)) == term {
    self.commit_to(max_index);
    true
}
```
The `term` argument is always the leader's current term.  The `== term` check is the A6 gate.

`RaftLog::commit_to` advances `committed` monotonically:
```rust
pub fn commit_to(&mut self, to_commit: u64) {
    if self.committed >= to_commit { return; }  // never decrease
    if self.last_index() < to_commit { fatal!(...) }
    self.committed = to_commit;
}
```
We model `commit_to` as `max committed toCommit` (the fatal branch is a panic guard, not part
of normal behaviour; its precondition `toCommit ≤ lastIndex` is enforced at the call site).

## What This File Provides

| ID   | Name                                 | Status    | Description                                                 |
|------|--------------------------------------|-----------|-------------------------------------------------------------|
| MC1  | `maybeCommit_ge_committed`           | ✅ proved | `maybeCommit` never decreases committed (monotone)          |
| MC2  | `maybeCommit_or`                     | ✅ proved | Result is either `committed` or `maxIndex`                  |
| MC3  | `maybeCommit_advances_iff`           | ✅ proved | Advances ↔ `maxIndex > committed ∧ log maxIndex = some term`|
| MC4  | `maybeCommit_term`                   | ✅ proved | **A6**: if advanced, `log (result) = some term`             |
| MC5  | `maybeCommit_no_advance_mismatch`    | ✅ proved | Term mismatch → no advance                                  |
| MC6  | `maybeCommit_no_advance_le`          | ✅ proved | `maxIndex ≤ committed` → no advance                         |
| MC7  | `maybeCommit_eq_maxIndex`            | ✅ proved | If advanced, result = `maxIndex`                            |
| MC8  | `maybeCommit_le_max`                 | ✅ proved | Result ≤ `max committed maxIndex`                           |
| MC9  | `maybeCommit_idempotent`             | ✅ proved | Applying `maybeCommit` twice = applying once                |
| MC10 | `commitTo_ge_committed`              | ✅ proved | `commitTo` is monotone                                      |
| MC11 | `commitTo_advances_iff`              | ✅ proved | `commitTo` advances iff `toCommit > committed`              |
| MC12 | `maybeCommit_eq_commitTo`            | ✅ proved | `maybeCommit` = `commitTo` when term check passes           |

**Sorry count**: 0.  All theorems are proved without `sorry`.

## Proof Chain

```
MC3 (advances_iff) ←──────────────────────────────────────────────────────────┐
          ↓                                                                    │
MC4 (A6 term safety): advanced → log[result] = some term                      │
          ↓                                                                    │
MC9 (idempotent): maybeCommit(maybeCommit(...)) = maybeCommit(...)             │
          ↓                                                                    │
MC12: when term matches, maybeCommit = commitTo (max committed maxIndex) ──────┘
```

## Connection to the Wider FV Portfolio

- **A6 gap**: This file provides the Lean formalisation of the term-safety check that has
  been flagged as the remaining "A6 obligation" since the FV project began.  Specifically,
  MC4 (`maybeCommit_term`) proves that `committed` is only advanced to an index whose log
  term equals the supplied `term` argument — exactly the Raft §5.4.2 constraint.

- **CommitRule.lean**: The `CommitRuleValid` predicate there captures the quorum-certification
  requirement (`hnew_cert`).  Combined with MC4, the full commit safety picture is:
  - The quorum has certified the entry (`CommitRuleValid` / CR5),
  - **and** the entry's term equals the leader's current term (`maybeCommit_term` / MC4).
  Together these close both the quorum-commit and term-safety gaps.

## Modelling Notes

- `LogTerm = Nat → Option Nat` from `FVSquad.FindConflict`.
- Terms are `Nat` (not `u64`); no overflow modelled.
- `zero_term_on_err_compacted` wrapper: we model this as requiring `log maxIndex = some term`
  (the log has an entry at that index with the exact term).  The compacted-entry case
  (returning 0) is handled by the model returning `committed` unchanged when `log maxIndex ≠ some term`.
- `commitTo`: the Rust fatal-if-beyond-lastIndex is a precondition on the caller; we model
  `commitTo` as `max committed toCommit` (the normal behaviour).
-/

namespace FVSquad.MaybeCommit

open FVSquad.FindConflict

/-! ## Definitions -/

/-- **maybeCommit** models `RaftLog::maybe_commit` from `src/raft_log.rs:530`.

    Advances `committed` to `maxIndex` iff:
    1. `maxIndex > committed` — advancing would actually increase committed.
    2. `log maxIndex = some term` — the entry at `maxIndex` has the expected term.

    The `term` argument is the leader's current term.  Condition 2 is the **A6 term safety
    check** (Raft §5.4.2): only entries from the current term may be directly committed. -/
def maybeCommit (log : LogTerm) (committed maxIndex term : Nat) : Nat :=
  if maxIndex > committed ∧ log maxIndex = some term then maxIndex else committed

/-- **commitTo** models `RaftLog::commit_to` from `src/raft_log.rs:304`.

    Advances committed to `max committed toCommit`.  The Rust `fatal!` for
    `toCommit > lastIndex` is a call-site precondition; the function itself just
    sets `committed = max committed toCommit`. -/
def commitTo (committed toCommit : Nat) : Nat :=
  max committed toCommit

/-! ## MC1: Monotonicity -/

/-- **MC1** (`maybeCommit_ge_committed`) — `maybeCommit` never decreases committed.

    This is the **monotonicity** guarantee: applying `maybeCommit` can only advance
    committed, never roll it back.  Mirrors the Rust "never decrease commit" comment
    in `commit_to`.

    **Significance**: directly corresponds to the `hcommitted_mono` hypothesis in
    `RaftReachable.step` (`RaftTrace.lean`), which requires committed indices to be
    non-decreasing across protocol steps. -/
theorem maybeCommit_ge_committed (log : LogTerm) (committed maxIndex term : Nat) :
    maybeCommit log committed maxIndex term ≥ committed := by
  simp only [maybeCommit]
  by_cases h : maxIndex > committed ∧ log maxIndex = some term
  · simp only [if_pos h]; omega
  · simp only [if_neg h]; exact Nat.le_refl _

/-! ## MC2: Result shape -/

/-- **MC2** (`maybeCommit_or`) — The result is always either `committed` or `maxIndex`.

    There is no intermediate value: `maybeCommit` either keeps committed unchanged or
    advances it all the way to `maxIndex`.  This mirrors Rust: the only assignment is
    `self.committed = to_commit` (= `maxIndex`). -/
theorem maybeCommit_or (log : LogTerm) (committed maxIndex term : Nat) :
    maybeCommit log committed maxIndex term = committed ∨
    maybeCommit log committed maxIndex term = maxIndex := by
  simp only [maybeCommit]
  by_cases h : maxIndex > committed ∧ log maxIndex = some term
  · have : (if maxIndex > committed ∧ log maxIndex = some term then maxIndex else committed) = maxIndex :=
      if_pos h
    exact Or.inr this
  · have : (if maxIndex > committed ∧ log maxIndex = some term then maxIndex else committed) = committed :=
      if_neg h
    exact Or.inl this

/-! ## MC3: Characterisation of advancement -/

/-- **MC3** (`maybeCommit_advances_iff`) — `maybeCommit` advances committed if and only
    if `maxIndex > committed` **and** the log entry at `maxIndex` has the expected term.

    This is the biconditional characterisation of when advancement occurs. -/
theorem maybeCommit_advances_iff (log : LogTerm) (committed maxIndex term : Nat) :
    maybeCommit log committed maxIndex term > committed ↔
    maxIndex > committed ∧ log maxIndex = some term := by
  simp only [maybeCommit]
  by_cases h : maxIndex > committed ∧ log maxIndex = some term
  · simp only [if_pos h]
    constructor
    · intro _; exact h
    · intro _; exact h.1
  · simp only [if_neg h]
    constructor
    · intro hlt; exact absurd hlt (Nat.lt_irrefl committed)
    · intro hc; exact absurd hc h

/-! ## MC4: A6 term safety -/

/-- **MC4** (`maybeCommit_term`) — **A6 term safety**: if `maybeCommit` advances
    committed, the log entry at the new committed index has exactly `term`.

    This is the Lean formalisation of Raft §5.4.2: a leader only commits an entry when
    the entry at `maxIndex` carries the leader's current term.  The A6 safety condition
    is a *necessary condition* for safety: without it, a stale entry from an old term
    might be committed, which could be overwritten by a future leader, violating the
    "no two nodes apply different entries at the same index" invariant.

    **Proof sketch**: if `maybeCommit` advanced, then by MC3, `log maxIndex = some term`.
    By MC7, result = `maxIndex`.  Therefore `log result = some term`. -/
theorem maybeCommit_term (log : LogTerm) (committed maxIndex term : Nat)
    (h : maybeCommit log committed maxIndex term > committed) :
    log (maybeCommit log committed maxIndex term) = some term := by
  simp only [maybeCommit] at *
  by_cases hc : maxIndex > committed ∧ log maxIndex = some term
  · simp only [if_pos hc] at *
    exact hc.2
  · simp only [if_neg hc] at h
    exact absurd h (Nat.lt_irrefl committed)

/-! ## MC5: No advance on term mismatch -/

/-- **MC5** (`maybeCommit_no_advance_mismatch`) — If the log entry at `maxIndex` does
    not have the expected term, `maybeCommit` does not advance committed.

    This is the key gate: the A6 check prevents committing entries from the wrong term. -/
theorem maybeCommit_no_advance_mismatch (log : LogTerm) (committed maxIndex term : Nat)
    (hne : log maxIndex ≠ some term) :
    maybeCommit log committed maxIndex term = committed := by
  simp only [maybeCommit]
  have : ¬(maxIndex > committed ∧ log maxIndex = some term) :=
    fun ⟨_, heq⟩ => absurd heq hne
  simp only [if_neg this]

/-! ## MC6: No advance when maxIndex ≤ committed -/

/-- **MC6** (`maybeCommit_no_advance_le`) — If `maxIndex ≤ committed`, `maybeCommit`
    does not advance committed.

    This is the first guard in `maybe_commit`: if `max_index > self.committed` is false,
    nothing changes.  Together with MC5, the two guards are exactly the conditions in MC3. -/
theorem maybeCommit_no_advance_le (log : LogTerm) (committed maxIndex term : Nat)
    (hle : maxIndex ≤ committed) :
    maybeCommit log committed maxIndex term = committed := by
  simp only [maybeCommit]
  have : ¬(maxIndex > committed ∧ log maxIndex = some term) :=
    fun ⟨hgt, _⟩ => absurd hgt (by omega)
  simp only [if_neg this]

/-! ## MC7: Result equals maxIndex when advanced -/

/-- **MC7** (`maybeCommit_eq_maxIndex`) — If `maybeCommit` advances committed, the result
    equals `maxIndex`.

    Combined with MC4: result = `maxIndex` and `log maxIndex = some term`. -/
theorem maybeCommit_eq_maxIndex (log : LogTerm) (committed maxIndex term : Nat)
    (h : maybeCommit log committed maxIndex term > committed) :
    maybeCommit log committed maxIndex term = maxIndex := by
  simp only [maybeCommit] at *
  by_cases hc : maxIndex > committed ∧ log maxIndex = some term
  · simp only [if_pos hc]
  · simp only [if_neg hc] at h
    exact absurd h (Nat.lt_irrefl committed)

/-! ## MC8: Result bounded above -/

/-- **MC8** (`maybeCommit_le_max`) — The result is at most `max committed maxIndex`.

    Together with MC1, this completely characterises the range:
    `committed ≤ maybeCommit ≤ max committed maxIndex`. -/
theorem maybeCommit_le_max (log : LogTerm) (committed maxIndex term : Nat) :
    maybeCommit log committed maxIndex term ≤ max committed maxIndex := by
  simp only [maybeCommit]
  by_cases h : maxIndex > committed ∧ log maxIndex = some term
  · simp only [if_pos h]; exact Nat.le_max_right _ _
  · simp only [if_neg h]; exact Nat.le_max_left _ _

/-! ## MC9: Idempotency -/

/-- **MC9** (`maybeCommit_idempotent`) — Applying `maybeCommit` twice with the same
    arguments is the same as applying it once.

    **Proof sketch**:
    - If conditions hold: first call returns `maxIndex`; second call has `maxIndex > maxIndex`
      false, so returns `maxIndex` unchanged.
    - If conditions fail: first call returns `committed`; second call has the same
      (failing) conditions, so returns `committed` again. -/
theorem maybeCommit_idempotent (log : LogTerm) (committed maxIndex term : Nat) :
    maybeCommit log (maybeCommit log committed maxIndex term) maxIndex term =
    maybeCommit log committed maxIndex term := by
  simp only [maybeCommit]
  by_cases h : maxIndex > committed ∧ log maxIndex = some term
  · -- First call returns maxIndex; second call: ¬(maxIndex > maxIndex)
    have hno : ¬(maxIndex > maxIndex ∧ log maxIndex = some term) :=
      fun ⟨hlt, _⟩ => Nat.lt_irrefl maxIndex hlt
    simp only [if_pos h, if_neg hno]
  · -- First call returns committed; second call has same failing condition
    simp only [if_neg h]

/-! ## MC10: commitTo monotonicity -/

/-- **MC10** (`commitTo_ge_committed`) — `commitTo` never decreases `committed`. -/
theorem commitTo_ge_committed (committed toCommit : Nat) :
    commitTo committed toCommit ≥ committed := by
  simp only [commitTo]; exact Nat.le_max_left _ _

/-! ## MC11: commitTo advancement condition -/

/-- **MC11** (`commitTo_advances_iff`) — `commitTo` advances committed iff `toCommit > committed`.

    This mirrors the Rust: `commit_to` only takes effect when `to_commit > self.committed`. -/
theorem commitTo_advances_iff (committed toCommit : Nat) :
    commitTo committed toCommit > committed ↔ toCommit > committed := by
  simp only [commitTo]
  omega

/-! ## MC12: Connection between maybeCommit and commitTo -/

/-- **MC12** (`maybeCommit_eq_commitTo`) — When the term check passes, `maybeCommit` is
    exactly `commitTo`.

    This theorem makes explicit that `maybeCommit` is `commitTo` guarded by the A6 term
    check.  When the guard passes, the two functions are definitionally equal. -/
theorem maybeCommit_eq_commitTo (log : LogTerm) (committed maxIndex term : Nat)
    (hterm : log maxIndex = some term) :
    maybeCommit log committed maxIndex term = commitTo committed maxIndex := by
  simp only [maybeCommit, commitTo]
  by_cases hgt : maxIndex > committed
  · have hcond : maxIndex > committed ∧ log maxIndex = some term := And.intro hgt hterm
    simp only [if_pos hcond]
    omega  -- max committed maxIndex = maxIndex when maxIndex > committed
  · have hno : ¬(maxIndex > committed ∧ log maxIndex = some term) :=
      fun hc => hgt hc.1
    simp only [if_neg hno]
    omega  -- max committed maxIndex = committed when maxIndex ≤ committed

end FVSquad.MaybeCommit
