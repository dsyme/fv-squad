import FVSquad.HasQuorum
import FVSquad.Progress

/-!
# Formal Specification: `ProgressTracker::quorum_recently_active`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises `ProgressTracker::quorum_recently_active` from `src/tracker.rs:336`,
the function that determines whether a quorum of nodes have recently been active from the
perspective of the leader.

## What `quorum_recently_active` does

```rust
pub fn quorum_recently_active(&mut self, perspective_of: u64) -> bool {
    let mut active = HashSet::new();
    for (id, pr) in &mut self.progress {
        if *id == perspective_of {
            pr.recent_active = true;
            active.insert(*id);
        } else if pr.recent_active {
            active.insert(*id);
            pr.recent_active = false;
        }
    }
    self.has_quorum(&active)
}
```

The leader (`perspective_of`) is **always** counted as active, regardless of its
`recent_active` flag. All other nodes are counted only if their flag is `true`.
The function then delegates to `has_quorum` to check if this active set forms a quorum.

## Modelling choices

- Models only the **read** semantics (which quorum check is performed).
- Ignores the **write** side-effects (setting `recent_active := false` on other nodes,
  marking `perspective_of` as `recent_active := true`). These affect future calls but
  not the current return value.
- `HashMap<u64, Progress>` → `List (Nat × Progress)` (order-independent, may have
  at most one entry per ID in well-formed inputs but the model allows duplicates).
- `u64` → `Nat`; no overflow modelled.
- Builds on `FVSquad.HasQuorum.hasQuorum` and `FVSquad.Progress.Progress`.

## Key properties formalised

| ID    | Name                                   | Description                                              |
|-------|----------------------------------------|----------------------------------------------------------|
| QRA1  | `isActive_nil`                         | No entries → nothing is active                           |
| QRA2  | `isActive_cons`                        | Unfold isActive over list head                           |
| QRA3  | `isActive_true_iff`                    | Characterisation of isActive as ∃                        |
| QRA4  | `isActive_self`                        | perspectiveOf is active if it has a progress entry       |
| QRA5  | `isActive_recentActive`                | recent_active=true nodes are always active               |
| QRA6  | `isActive_false_absent`                | Node absent from entries is not active                   |
| QRA7  | `isActive_append`                      | isActive distributes over list append                    |
| QRA8  | `overlapCount_active_nil`              | Overlap with empty entries = 0                           |
| QRA9  | `isActive_monotone_overlap`            | More active entries → ≥ overlap count                    |
| QRA10 | `quorumRecentlyActive_def`             | Definitional unfolding                                   |
| QRA11 | `quorumRecentlyActive_nil_voters`      | Empty voters → always quorate                            |
| QRA12 | `quorumRecentlyActive_nil_entries`     | Empty entries: quorum iff no voters                      |
| QRA13 | `quorumRecentlyActive_singleton_self`  | Single-voter = leader in entries → always quorate        |
| QRA14 | `quorumRecentlyActive_all_active`      | All voters have active entries → quorum                  |
| QRA15 | `quorumRecentlyActive_monotone`        | More active entries preserves quorum                     |
-/

namespace FVSquad.QuorumRecentlyActive

open FVSquad.Progress

-- ---------------------------------------------------------------------------
-- Types and core definitions
-- ---------------------------------------------------------------------------

/-- `isActive entries perspectiveOf n` is `true` iff node `n` should be counted in
    the "recently active" set:
    - Either `n = perspectiveOf` (the leader is always active), or
    - `n` has an entry in `entries` with `recent_active = true`.

    This is the predicate passed to `hasQuorum` by `quorum_recently_active`.

    **Abstraction**: the Rust code uses `HashMap<u64, Progress>` and processes entries
    with side-effects; here we model only the read-side (what set is formed). -/
def isActive (entries : List (Nat × Progress)) (perspectiveOf : Nat) (n : Nat) : Bool :=
  entries.any (fun e => e.1 == n && (e.1 == perspectiveOf || e.2.recent_active))

/-- Pure functional model of `ProgressTracker::quorum_recently_active`.

    Returns `true` iff the recently-active set (leader + recent_active nodes) forms
    a majority quorum of `voters`. -/
def quorumRecentlyActive (voters : List Nat) (entries : List (Nat × Progress))
    (perspectiveOf : Nat) : Bool :=
  hasQuorum voters (isActive entries perspectiveOf)

-- ---------------------------------------------------------------------------
-- Evaluations
-- ---------------------------------------------------------------------------

section Eval

private def mkPr (ra : Bool) : Progress :=
  { matched := 0, next_idx := 1, state := .Probe, paused := false,
    pending_snapshot := 0, pending_request_snapshot := 0,
    recent_active := ra, ins_full := false }

-- 3 voters. Leader=1 (always active), node 2 (recent_active=true), node 3 (recent_active=false).
-- Active set: {1, 2}. Overlap with [1,2,3] = 2 ≥ majority(3) = 2 → true.
#eval quorumRecentlyActive [1, 2, 3]
  [(1, mkPr false), (2, mkPr true), (3, mkPr false)] 1  -- expected: true

-- 3 voters. Leader=1, nodes 2 and 3 inactive. Active set: {1}. Overlap = 1 < 2 → false.
#eval quorumRecentlyActive [1, 2, 3]
  [(1, mkPr false), (2, mkPr false), (3, mkPr false)] 1  -- expected: false

-- Single voter = leader. Active set always includes leader → overlap 1 ≥ majority(1)=1 → true.
#eval quorumRecentlyActive [1] [(1, mkPr false)] 1  -- expected: true

-- Empty voters → vacuously true.
#eval quorumRecentlyActive [] [(1, mkPr false)] 1  -- expected: true

-- Leader not in entries, but leader is not a voter either → hasQuorum checks voters.
-- voters=[2,3], entries=[], active set={}. overlap=0 < 2 → false.
#eval quorumRecentlyActive [2, 3] [] 1  -- expected: false

end Eval

-- ---------------------------------------------------------------------------
-- Lemmas on isActive
-- ---------------------------------------------------------------------------

/-- QRA1: Empty entries → nothing is active. -/
@[simp] theorem isActive_nil (perspectiveOf n : Nat) :
    isActive [] perspectiveOf n = false := rfl

/-- QRA2: Unfolding rule for isActive on a cons. -/
@[simp] theorem isActive_cons (e : Nat × Progress) (es : List (Nat × Progress))
    (perspectiveOf n : Nat) :
    isActive (e :: es) perspectiveOf n =
      (e.1 == n && (e.1 == perspectiveOf || e.2.recent_active) ||
       isActive es perspectiveOf n) := rfl

/-- QRA3: `isActive entries perspectiveOf n = true` iff some entry has id `n` and is active
    (either because it is the leader, or because `recent_active = true`). -/
theorem isActive_true_iff (entries : List (Nat × Progress)) (perspectiveOf n : Nat) :
    isActive entries perspectiveOf n = true ↔
    ∃ e ∈ entries, e.1 = n ∧ (e.1 = perspectiveOf ∨ e.2.recent_active = true) := by
  unfold isActive
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, heq⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at heq
    exact ⟨e, he, heq.1, heq.2⟩
  · rintro ⟨e, he, hid, hcond⟩
    refine ⟨e, he, ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    exact ⟨hid, hcond⟩

/-- QRA4: If `(perspectiveOf, pr)` is in `entries`, then `perspectiveOf` is active.
    The leader is always counted as active in `quorum_recently_active`. -/
theorem isActive_self (entries : List (Nat × Progress)) (perspectiveOf : Nat)
    (pr : Progress) (h : (perspectiveOf, pr) ∈ entries) :
    isActive entries perspectiveOf perspectiveOf = true := by
  rw [isActive_true_iff]
  exact ⟨(perspectiveOf, pr), h, rfl, Or.inl rfl⟩

/-- QRA5: Any node with `recent_active = true` is in the active set. -/
theorem isActive_recentActive (entries : List (Nat × Progress)) (perspectiveOf n : Nat)
    (pr : Progress) (hmem : (n, pr) ∈ entries) (hact : pr.recent_active = true) :
    isActive entries perspectiveOf n = true := by
  rw [isActive_true_iff]
  exact ⟨(n, pr), hmem, rfl, Or.inr hact⟩

/-- QRA6: If node `n` has no entry in `entries`, it is not active. -/
theorem isActive_false_absent (entries : List (Nat × Progress)) (perspectiveOf n : Nat)
    (h : ∀ e ∈ entries, e.1 ≠ n) :
    isActive entries perspectiveOf n = false := by
  cases hact : isActive entries perspectiveOf n
  · rfl
  · rw [isActive_true_iff] at hact
    obtain ⟨e, he, hid, _⟩ := hact
    exact absurd hid (h e he)

/-- QRA7: `isActive` distributes over list append. -/
theorem isActive_append (es1 es2 : List (Nat × Progress)) (perspectiveOf n : Nat) :
    isActive (es1 ++ es2) perspectiveOf n =
    (isActive es1 perspectiveOf n || isActive es2 perspectiveOf n) := by
  unfold isActive
  simp [List.any_append]

-- ---------------------------------------------------------------------------
-- Overlap-count lemmas
-- ---------------------------------------------------------------------------

/-- QRA8: With empty entries, the overlap count is 0 for any voter list. -/
theorem overlapCount_active_nil (voters : List Nat) (perspectiveOf : Nat) :
    overlapCount voters (isActive [] perspectiveOf) = 0 := by
  induction voters with
  | nil => simp [overlapCount]
  | cons v vs ih => simp [overlapCount_cons, ih]

/-- QRA9: If one active predicate implies the other, the overlap is non-decreasing.
    More entries ⊇ fewer entries → at least as many active nodes. -/
theorem isActive_monotone_overlap (voters : List Nat) (es1 es2 : List (Nat × Progress))
    (perspectiveOf : Nat)
    (h : ∀ n, isActive es1 perspectiveOf n = true → isActive es2 perspectiveOf n = true) :
    overlapCount voters (isActive es1 perspectiveOf) ≤
    overlapCount voters (isActive es2 perspectiveOf) := by
  apply overlapCount_monotone
  exact h

-- ---------------------------------------------------------------------------
-- Main theorems on quorumRecentlyActive
-- ---------------------------------------------------------------------------

/-- QRA10: Definitional unfolding — `quorumRecentlyActive` is exactly `hasQuorum` on the
    active predicate. -/
@[simp] theorem quorumRecentlyActive_def (voters : List Nat)
    (entries : List (Nat × Progress)) (perspectiveOf : Nat) :
    quorumRecentlyActive voters entries perspectiveOf =
    hasQuorum voters (isActive entries perspectiveOf) := rfl

/-- QRA11: Empty voters → always quorate (vacuous majority). -/
@[simp] theorem quorumRecentlyActive_nil_voters (entries : List (Nat × Progress))
    (perspectiveOf : Nat) :
    quorumRecentlyActive [] entries perspectiveOf = true := rfl

/-- QRA12: Empty entries → quorum iff the voter list is empty.
    With no progress entries, no node is active, so a majority can only be reached
    vacuously (empty voter list). -/
theorem quorumRecentlyActive_nil_entries (voters : List Nat) (perspectiveOf : Nat) :
    quorumRecentlyActive voters [] perspectiveOf = voters.isEmpty := by
  unfold quorumRecentlyActive
  cases voters with
  | nil => simp [hasQuorum_nil]
  | cons v vs =>
    simp only [List.isEmpty_cons]
    exact hasQuorum_false_of_none_in v vs (isActive [] perspectiveOf)
      (fun w _ => isActive_nil perspectiveOf w)

/-- QRA13: **Leader-as-single-voter**: if `perspectiveOf` is the only voter and has a
    progress entry, the quorum is always satisfied.
    The leader always counts itself as active. -/
theorem quorumRecentlyActive_singleton_self (perspectiveOf : Nat)
    (entries : List (Nat × Progress)) (pr : Progress)
    (h : (perspectiveOf, pr) ∈ entries) :
    quorumRecentlyActive [perspectiveOf] entries perspectiveOf = true := by
  simp only [quorumRecentlyActive_def]
  exact hasQuorum_singleton_self perspectiveOf (isActive entries perspectiveOf)
    (isActive_self entries perspectiveOf pr h)

/-- QRA14: If every voter has an active entry (either as `perspectiveOf` or with
    `recent_active = true`), the quorum is satisfied. -/
theorem quorumRecentlyActive_all_active (voters : List Nat)
    (entries : List (Nat × Progress)) (perspectiveOf : Nat)
    (h : ∀ voter ∈ voters, isActive entries perspectiveOf voter = true) :
    quorumRecentlyActive voters entries perspectiveOf = true := by
  simp only [quorumRecentlyActive_def]
  exact hasQuorum_true_of_all_in voters (isActive entries perspectiveOf) h

/-- QRA15: Monotonicity: if entries `es2` activates at least every node that `es1` does,
    then quorum is preserved when switching from `es1` to `es2`. -/
theorem quorumRecentlyActive_monotone (voters : List Nat)
    (es1 es2 : List (Nat × Progress)) (perspectiveOf : Nat)
    (h : ∀ n, isActive es1 perspectiveOf n = true → isActive es2 perspectiveOf n = true)
    (hq : quorumRecentlyActive voters es1 perspectiveOf = true) :
    quorumRecentlyActive voters es2 perspectiveOf = true := by
  simp only [quorumRecentlyActive_def] at *
  exact hasQuorum_monotone voters (isActive es1 perspectiveOf) (isActive es2 perspectiveOf) h hq

end FVSquad.QuorumRecentlyActive
