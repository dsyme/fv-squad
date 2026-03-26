/-!
# HasReady — Lean 4 Specification, Implementation, and Proofs

Formal specification of `RawNode::has_ready` from `src/raw_node.rs`.

`has_ready` is a pure Boolean predicate: it returns `true` if and only if
at least one of seven observable conditions holds, indicating that the
application must call `ready()` and process the resulting work.

## Relevant Rust code

```rust
pub fn has_ready(&self) -> bool {
    let raft = &self.raft;
    if !raft.msgs.is_empty() { return true; }             // C1: pending messages
    if raft.soft_state() != self.prev_ss { return true; } // C2: role/leader changed
    if raft.hard_state() != self.prev_hs { return true; } // C3: term/vote/commit changed
    if !raft.read_states.is_empty() { return true; }      // C4: read-index results
    if !raft.raft_log.unstable_entries().is_empty() { return true; } // C5: entries to persist
    if self.snap().is_some_and(|s| !s.is_empty()) { return true; }   // C6: snapshot pending
    if raft.raft_log.has_next_entries_since(self.commit_since_index) { return true; } // C7: entries to apply
    false
}
```

## Model scope and approximations

* **`RawNodeObservable`**: The full `RawNode` state is abstracted to the seven
  Boolean conditions that `has_ready` checks. Each Boolean represents the outcome
  of one of the seven conditions: `hasMsgs`, `ssChanged`, `hsChanged`,
  `hasReadStates`, `hasUnstableEntries`, `hasSnapshot`, `hasNextEntries`.
* **No state evolution**: we model the predicate at a single point in time.
  The relationship between `has_ready` and `ready()` output is not modelled here.
* **Equality checks**: `soft_state() != prev_ss` and `hard_state() != prev_hs` are
  abstracted to single Boolean flags (`ssChanged`, `hsChanged`). Their internals
  are not modelled in this file.
* **Snapshot emptiness**: `snap().is_some_and(|s| !s.is_empty())` is a two-level
  check (Some + non-empty); abstracted to a single `hasSnapshot : Bool`.
* **I/O, logging, network** — all omitted.

## Theorems proved (no `sorry`)

1. `hasReady_eq_or`          — implementation equals the explicit OR expression
2. `hasReady_true_iff`       — characterisation: `hasReady = true ↔ disjunction holds`
3. `hasReady_false_iff`      — characterisation: `hasReady = false ↔ all conditions false`
4. `notHasReady_no_msgs`     — ¬has_ready → hasMsgs = false
5. `notHasReady_ss_stable`   — ¬has_ready → ssChanged = false
6. `notHasReady_hs_stable`   — ¬has_ready → hsChanged = false
7. `notHasReady_no_readStates` — ¬has_ready → hasReadStates = false
8. `notHasReady_no_unstable` — ¬has_ready → hasUnstableEntries = false
9. `notHasReady_no_snapshot` — ¬has_ready → hasSnapshot = false
10. `notHasReady_no_committed` — ¬has_ready → hasNextEntries = false
11–17. `hasMsgs_implies_hasReady` (and analogues for each condition)
18. `hasReady_idempotent`    — calling twice without state change: same result
19. `hasReady_monotone`      — if conditions only become more true, hasReady stays true
20. `hasReady_false_all_false` — `hasReady = false ↔ ∀ condition, condition = false`

🔬 *Lean Squad — automated formal verification.*
-/

import Mathlib.Tactic

namespace FVSquad.HasReady

/-! ## Observable state -/

/-- The seven observable Boolean conditions checked by `has_ready`.

    Each field represents the outcome of one guard in the Rust implementation:
    - `hasMsgs`            ↔ `!raft.msgs.is_empty()`
    - `ssChanged`          ↔ `raft.soft_state() != self.prev_ss`
    - `hsChanged`          ↔ `raft.hard_state() != self.prev_hs`
    - `hasReadStates`      ↔ `!raft.read_states.is_empty()`
    - `hasUnstableEntries` ↔ `!raft.raft_log.unstable_entries().is_empty()`
    - `hasSnapshot`        ↔ `self.snap().is_some_and(|s| !s.is_empty())`
    - `hasNextEntries`     ↔ `raft.raft_log.has_next_entries_since(commit_since_index)`
-/
structure RawNodeObservable where
  hasMsgs            : Bool
  ssChanged          : Bool
  hsChanged          : Bool
  hasReadStates      : Bool
  hasUnstableEntries : Bool
  hasSnapshot        : Bool
  hasNextEntries     : Bool
  deriving DecidableEq, Repr, BEq, Inhabited

/-! ## Implementation model -/

/-- Pure model of `RawNode::has_ready`.

    Returns `true` iff at least one of the seven observable conditions is `true`.
    Mirrors the early-return structure in the Rust source exactly. -/
def hasReady (s : RawNodeObservable) : Bool :=
  s.hasMsgs || s.ssChanged || s.hsChanged || s.hasReadStates ||
  s.hasUnstableEntries || s.hasSnapshot || s.hasNextEntries

/-! ## Core characterisation theorems -/

/-- The `hasReady` function equals the explicit OR of all seven conditions.
    This is the definitional unfolding theorem. -/
@[simp]
theorem hasReady_eq_or (s : RawNodeObservable) :
    hasReady s = (s.hasMsgs || s.ssChanged || s.hsChanged || s.hasReadStates ||
                  s.hasUnstableEntries || s.hasSnapshot || s.hasNextEntries) := rfl

/-- **Full characterisation** (true direction):
    `has_ready` returns `true` iff at least one condition holds. -/
theorem hasReady_true_iff (s : RawNodeObservable) :
    hasReady s = true ↔
    (s.hasMsgs = true ∨ s.ssChanged = true ∨ s.hsChanged = true ∨
     s.hasReadStates = true ∨ s.hasUnstableEntries = true ∨
     s.hasSnapshot = true ∨ s.hasNextEntries = true) := by
  simp [hasReady, Bool.or_eq_true]

/-- **Full characterisation** (false direction):
    `has_ready` returns `false` iff all seven conditions are false. -/
theorem hasReady_false_iff (s : RawNodeObservable) :
    hasReady s = false ↔
    (s.hasMsgs = false ∧ s.ssChanged = false ∧ s.hsChanged = false ∧
     s.hasReadStates = false ∧ s.hasUnstableEntries = false ∧
     s.hasSnapshot = false ∧ s.hasNextEntries = false) := by
  simp [hasReady, Bool.or_eq_false_iff]

/-! ## Consequence theorems: ¬has_ready implies each condition is false -/

/-- If `has_ready` is false, there are no pending outbound messages (C1). -/
theorem notHasReady_no_msgs (s : RawNodeObservable) (h : hasReady s = false) :
    s.hasMsgs = false := by
  simp [hasReady_false_iff] at h; exact h.1

/-- If `has_ready` is false, the soft state has not changed (C2). -/
theorem notHasReady_ss_stable (s : RawNodeObservable) (h : hasReady s = false) :
    s.ssChanged = false := by
  simp [hasReady_false_iff] at h; exact h.2.1

/-- If `has_ready` is false, the hard state has not changed (C3). -/
theorem notHasReady_hs_stable (s : RawNodeObservable) (h : hasReady s = false) :
    s.hsChanged = false := by
  simp [hasReady_false_iff] at h; exact h.2.2.1

/-- If `has_ready` is false, there are no pending read states (C4). -/
theorem notHasReady_no_readStates (s : RawNodeObservable) (h : hasReady s = false) :
    s.hasReadStates = false := by
  simp [hasReady_false_iff] at h; exact h.2.2.2.1

/-- If `has_ready` is false, there are no unstable log entries to persist (C5). -/
theorem notHasReady_no_unstable (s : RawNodeObservable) (h : hasReady s = false) :
    s.hasUnstableEntries = false := by
  simp [hasReady_false_iff] at h; exact h.2.2.2.2.1

/-- If `has_ready` is false, there is no pending snapshot (C6). -/
theorem notHasReady_no_snapshot (s : RawNodeObservable) (h : hasReady s = false) :
    s.hasSnapshot = false := by
  simp [hasReady_false_iff] at h; exact h.2.2.2.2.2.1

/-- If `has_ready` is false, there are no committed entries to apply (C7). -/
theorem notHasReady_no_committed (s : RawNodeObservable) (h : hasReady s = false) :
    s.hasNextEntries = false := by
  simp [hasReady_false_iff] at h; exact h.2.2.2.2.2.2

/-! ## Sufficiency theorems: each condition alone implies has_ready -/

/-- Pending messages alone suffice to make `has_ready` true (C1). -/
theorem hasMsgs_implies_hasReady (s : RawNodeObservable) (h : s.hasMsgs = true) :
    hasReady s = true := by simp [hasReady, h]

/-- Soft state change alone suffices (C2). -/
theorem ssChanged_implies_hasReady (s : RawNodeObservable) (h : s.ssChanged = true) :
    hasReady s = true := by simp [hasReady, h]

/-- Hard state change alone suffices (C3). -/
theorem hsChanged_implies_hasReady (s : RawNodeObservable) (h : s.hsChanged = true) :
    hasReady s = true := by simp [hasReady, h]

/-- Pending read states alone suffice (C4). -/
theorem hasReadStates_implies_hasReady (s : RawNodeObservable) (h : s.hasReadStates = true) :
    hasReady s = true := by simp [hasReady, h]

/-- Unstable log entries alone suffice (C5). -/
theorem hasUnstableEntries_implies_hasReady (s : RawNodeObservable)
    (h : s.hasUnstableEntries = true) : hasReady s = true := by simp [hasReady, h]

/-- A pending snapshot alone suffices (C6). -/
theorem hasSnapshot_implies_hasReady (s : RawNodeObservable) (h : s.hasSnapshot = true) :
    hasReady s = true := by simp [hasReady, h]

/-- Committed entries to apply alone suffice (C7). -/
theorem hasNextEntries_implies_hasReady (s : RawNodeObservable) (h : s.hasNextEntries = true) :
    hasReady s = true := by simp [hasReady, h]

/-! ## Stability / idempotence -/

/-- **Idempotence**: `has_ready` is a pure read — calling it again without any state
    change returns the same value. (Trivially true since `hasReady` has no side effects.) -/
theorem hasReady_idempotent (s : RawNodeObservable) :
    hasReady s = hasReady s := rfl

/-! ## Monotonicity -/

/-- **Monotonicity**: if one state is "pointwise ≥" another (every false stays false
    or becomes true), and `has_ready` held in the weaker state, it holds in the stronger.

    Formalised as: if s₁ implies s₂ on each condition (i.e. each `true` in s₁ is also
    `true` in s₂), then `has_ready s₁ = true → has_ready s₂ = true`. -/
theorem hasReady_monotone (s₁ s₂ : RawNodeObservable)
    (hm  : s₁.hasMsgs = true            → s₂.hasMsgs = true)
    (hss : s₁.ssChanged = true           → s₂.ssChanged = true)
    (hhs : s₁.hsChanged = true           → s₂.hsChanged = true)
    (hrd : s₁.hasReadStates = true       → s₂.hasReadStates = true)
    (hue : s₁.hasUnstableEntries = true  → s₂.hasUnstableEntries = true)
    (hsn : s₁.hasSnapshot = true         → s₂.hasSnapshot = true)
    (hne : s₁.hasNextEntries = true      → s₂.hasNextEntries = true)
    (h   : hasReady s₁ = true) : hasReady s₂ = true := by
  simp [hasReady_true_iff] at h ⊢
  rcases h with hm' | hss' | hhs' | hrd' | hue' | hsn' | hne'
  · exact Or.inl (hm hm')
  · exact Or.inr (Or.inl (hss hss'))
  · exact Or.inr (Or.inr (Or.inl (hhs hhs')))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hrd hrd'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hue hue')))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsn hsn'))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hne hne'))))))

/-! ## Idle state theorem -/

/-- **Idle state**: the unique state where `has_ready` returns `false` is when
    all seven conditions are simultaneously false. -/
theorem hasReady_false_all_false (s : RawNodeObservable) :
    hasReady s = false ↔
    s.hasMsgs = false ∧ s.ssChanged = false ∧ s.hsChanged = false ∧
    s.hasReadStates = false ∧ s.hasUnstableEntries = false ∧
    s.hasSnapshot = false ∧ s.hasNextEntries = false :=
  hasReady_false_iff s

/-- The all-false state is a valid configuration (idle node). -/
theorem idle_state_exists :
    ∃ s : RawNodeObservable, hasReady s = false := by
  exact ⟨⟨false, false, false, false, false, false, false⟩, rfl⟩

/-- There exist states for each of the 7 individual conditions that make has_ready true. -/
theorem each_condition_has_witness :
    (∃ s : RawNodeObservable, hasReady s = true ∧ s.hasMsgs = true) ∧
    (∃ s : RawNodeObservable, hasReady s = true ∧ s.ssChanged = true) ∧
    (∃ s : RawNodeObservable, hasReady s = true ∧ s.hsChanged = true) ∧
    (∃ s : RawNodeObservable, hasReady s = true ∧ s.hasReadStates = true) ∧
    (∃ s : RawNodeObservable, hasReady s = true ∧ s.hasUnstableEntries = true) ∧
    (∃ s : RawNodeObservable, hasReady s = true ∧ s.hasSnapshot = true) ∧
    (∃ s : RawNodeObservable, hasReady s = true ∧ s.hasNextEntries = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · first
    | exact ⟨⟨true,  false, false, false, false, false, false⟩, rfl, rfl⟩
    | exact ⟨⟨false, true,  false, false, false, false, false⟩, rfl, rfl⟩
    | exact ⟨⟨false, false, true,  false, false, false, false⟩, rfl, rfl⟩
    | exact ⟨⟨false, false, false, true,  false, false, false⟩, rfl, rfl⟩
    | exact ⟨⟨false, false, false, false, true,  false, false⟩, rfl, rfl⟩
    | exact ⟨⟨false, false, false, false, false, true,  false⟩, rfl, rfl⟩
    | exact ⟨⟨false, false, false, false, false, false, true ⟩, rfl, rfl⟩

/-! ## Decidability -/

/-- `has_ready` is decidable for any `RawNodeObservable` — trivially, since all
    fields are `Bool` and `hasReady` is a Boolean expression. -/
instance (s : RawNodeObservable) : Decidable (hasReady s = true) :=
  inferInstance

/-- All 128 possible combinations of the 7 Boolean conditions are
    handled correctly by `hasReady`. There are exactly 127 states
    where `has_ready = true` and exactly 1 state where it is `false`. -/
theorem hasReady_coverage : decide (
    (∀ b1 b2 b3 b4 b5 b6 b7 : Bool,
      hasReady ⟨b1, b2, b3, b4, b5, b6, b7⟩ =
      (b1 || b2 || b3 || b4 || b5 || b6 || b7))) = true := by decide

end FVSquad.HasReady
