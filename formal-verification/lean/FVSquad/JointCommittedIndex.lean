import FVSquad.CommittedIndex

/-!
# JointCommittedIndex — Lean 4 Specification and Implementation Model

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Formal specification and proofs for `Configuration::committed_index` from
`src/quorum/joint.rs` — the joint-quorum committed-index computation.

## What `joint committed_index` does

```rust
pub fn committed_index(&self, use_group_commit: bool, l: &impl AckedIndexer) -> (u64, bool) {
    let (i_idx, i_use_gc) = self.incoming.committed_index(use_group_commit, l);
    let (o_idx, o_use_gc) = self.outgoing.committed_index(use_group_commit, l);
    (cmp::min(i_idx, o_idx), i_use_gc && o_use_gc)
}
```

A joint quorum commits an index only when **both** constituent majority quorums
commit it.  The joint committed index is therefore the **minimum** of the two
constituent committed indices.

## Modelling choices

* We model `jointCommittedIndex` directly as
  `min (committedIndex incoming acked) (committedIndex outgoing acked)`.
* The `use_group_commit` flag and the `bool` component of the return tuple are
  omitted — this models the non-group-commit path only.
* **Empty-outgoing divergence**: when `outgoing = []`, the Rust implementation
  returns `u64::MAX` for `outgoing.committed_index`, so `min(i_idx, MAX) = i_idx`.
  Our Lean model uses `committedIndex [] _ = 0` (cf. `committedIndex_empty`), so
  the result is `min(ci_in, 0) = 0`, not `ci_in`.  This is a known approximation;
  see `CORRESPONDENCE.md` for the full divergence analysis.
* All other approximations from `CommittedIndex.lean` (voter-list vs. HashSet,
  `u64` → `Nat`, pure AckedFn model) apply here unchanged.
-/

open FVSquad.CommittedIndex

namespace FVSquad.JointCommittedIndex

/-! ## Core definition -/

/-- The jointly committed index for a two-majority-group configuration.
    Mirrors `Configuration::committed_index` in `src/quorum/joint.rs:50`
    (non-group-commit path only).  An index is jointly committed when it is
    committed by **both** constituent majority quorums. -/
def jointCommittedIndex
    (incoming outgoing : List Nat)
    (acked : AckedFn) : Nat :=
  min (committedIndex incoming acked) (committedIndex outgoing acked)

/-! ## Evaluations -/

section Eval

-- Empty config on both sides → 0
#eval jointCommittedIndex [] [] (fun _ => 0)
-- (= 0 ✓)

-- Single voter in each group, both acked at index 5 → 5
#eval jointCommittedIndex [1] [2] (fun _ => 5)
-- (= 5 ✓)

-- 3-voter incoming (ci=2), 2-voter outgoing (ci=2) → 2
-- incoming: [1,2,3] ack [2,2,2]; majority(3)=2; sorted=[2,2,2]; ci=2
-- outgoing: [4,5] ack [2,2]; majority(2)=2; sorted=[2,2]; ci=2; joint=min(2,2)=2
#eval jointCommittedIndex [1,2,3] [4,5] (fun _ => 2)
-- (= 2 ✓)

-- incoming ci = 5, outgoing ci = 3 → joint = 3
-- outgoing: [4,5] ack [3,5]; majority(2)=2; sorted=[5,3]; ci=3
-- incoming: [1,2,3] ack 5; ci=5; joint=min(5,3)=3
#eval jointCommittedIndex [1,2,3] [4,5] (fun v => if v == 4 then 3 else 5)
-- (= 3 ✓)

end Eval

/-! ## Bound lemmas (JCI1–JCI3) -/

/-- **JCI1** — `jointCommittedIndex` is at most `committedIndex incoming`. -/
theorem jointCommittedIndex_le_in (incoming outgoing : List Nat) (acked : AckedFn) :
    jointCommittedIndex incoming outgoing acked ≤ committedIndex incoming acked :=
  Nat.min_le_left _ _

/-- **JCI2** — `jointCommittedIndex` is at most `committedIndex outgoing`. -/
theorem jointCommittedIndex_le_out (incoming outgoing : List Nat) (acked : AckedFn) :
    jointCommittedIndex incoming outgoing acked ≤ committedIndex outgoing acked :=
  Nat.min_le_right _ _

/-- **JCI3** — Any `k` bounded above by both constituent committed indices is also
    bounded by `jointCommittedIndex`.  Together with JCI1–JCI2 this characterises
    `jointCommittedIndex` as the infimum of the two constituent indices. -/
theorem jointCommittedIndex_ge_lower_bound (incoming outgoing : List Nat) (acked : AckedFn)
    (k : Nat)
    (hin : k ≤ committedIndex incoming acked)
    (hout : k ≤ committedIndex outgoing acked) :
    k ≤ jointCommittedIndex incoming outgoing acked :=
  Nat.le_min.mpr ⟨hin, hout⟩

/-! ## Safety theorems (JCI4–JCI5)

The joint committed index is safe in both constituent quorums: a majority of
*incoming* voters and a majority of *outgoing* voters have each individually
acknowledged at least `jointCommittedIndex`. -/

/-- **JCI4 — Safety for incoming**: if `incoming` is non-empty, a majority of its
    voters have acked ≥ `jointCommittedIndex`.

    Proof sketch: JCI1 gives `jci ≤ ci_in`.  `countGe_antitone` then gives
    `countGe(ci_in) ≤ countGe(jci)`.  `committedIndex_safety` gives
    `majority ≤ countGe(ci_in)`.  Chaining yields the result. -/
theorem jointCommittedIndex_safety_in (incoming outgoing : List Nat) (acked : AckedFn)
    (hn : 0 < incoming.length) :
    majority incoming.length ≤ countGe incoming acked (jointCommittedIndex incoming outgoing acked) := by
  have hle := jointCommittedIndex_le_in incoming outgoing acked
  have hsafe := committedIndex_safety incoming acked hn
  have hmono := countGe_antitone incoming acked
      (jointCommittedIndex incoming outgoing acked) (committedIndex incoming acked) hle
  omega

/-- **JCI5 — Safety for outgoing**: if `outgoing` is non-empty, a majority of its
    voters have acked ≥ `jointCommittedIndex`. -/
theorem jointCommittedIndex_safety_out (incoming outgoing : List Nat) (acked : AckedFn)
    (hn : 0 < outgoing.length) :
    majority outgoing.length ≤ countGe outgoing acked (jointCommittedIndex incoming outgoing acked) := by
  have hle := jointCommittedIndex_le_out incoming outgoing acked
  have hsafe := committedIndex_safety outgoing acked hn
  have hmono := countGe_antitone outgoing acked
      (jointCommittedIndex incoming outgoing acked) (committedIndex outgoing acked) hle
  omega

/-! ## Maximality theorem (JCI6)

No index larger than `jointCommittedIndex` is simultaneously acknowledged by a
majority of both groups. -/

/-- **JCI6 — Maximality**: if `k > jointCommittedIndex`, then at least one group
    lacks a majority of voters who have acked `k`.

    Proof sketch: `k > min(ci_in, ci_out)` implies `k > ci_in` or `k > ci_out`
    (whichever is smaller).  `committedIndex_maximality` then closes the goal for
    that group.  The empty-list case is vacuously handled by `committedIndex_maximality`
    itself (majority 0 = 1 > 0 = countGe [] _ k). -/
theorem jointCommittedIndex_maximality (incoming outgoing : List Nat) (acked : AckedFn)
    (k : Nat)
    (hk : jointCommittedIndex incoming outgoing acked < k) :
    countGe incoming acked k < majority incoming.length ∨
    countGe outgoing acked k < majority outgoing.length := by
  unfold jointCommittedIndex at hk
  by_cases h : committedIndex incoming acked ≤ committedIndex outgoing acked
  · rw [Nat.min_eq_left h] at hk
    exact Or.inl (committedIndex_maximality incoming acked k hk)
  · have hlt : committedIndex outgoing acked < committedIndex incoming acked :=
      Nat.lt_of_not_le h
    rw [Nat.min_eq_right (Nat.le_of_lt hlt)] at hk
    exact Or.inr (committedIndex_maximality outgoing acked k hk)

/-! ## Monotonicity theorem (JCI7) -/

/-- **JCI7 — Monotonicity**: if every voter's acked index is non-decreasing (pointwise),
    then `jointCommittedIndex` is non-decreasing.

    Proof: apply `committedIndex_mono` to each component independently;
    since both components are non-decreasing, so is their minimum. -/
theorem jointCommittedIndex_mono (incoming outgoing : List Nat) (acked1 acked2 : AckedFn)
    (hle : ∀ v, acked1 v ≤ acked2 v) :
    jointCommittedIndex incoming outgoing acked1 ≤ jointCommittedIndex incoming outgoing acked2 := by
  unfold jointCommittedIndex
  apply Nat.le_min.mpr
  constructor
  · calc min (committedIndex incoming acked1) (committedIndex outgoing acked1)
        ≤ committedIndex incoming acked1 := Nat.min_le_left _ _
      _ ≤ committedIndex incoming acked2 := committedIndex_mono incoming acked1 acked2 hle
  · calc min (committedIndex incoming acked1) (committedIndex outgoing acked1)
        ≤ committedIndex outgoing acked1 := Nat.min_le_right _ _
      _ ≤ committedIndex outgoing acked2 := committedIndex_mono outgoing acked1 acked2 hle

/-! ## Degenerate cases (JCI8–JCI10) -/

/-- **JCI8** — When all voters have acked index 0, the joint committed index is 0. -/
theorem jointCommittedIndex_all_zero (incoming outgoing : List Nat) :
    jointCommittedIndex incoming outgoing (fun _ => 0) = 0 := by
  unfold jointCommittedIndex
  rw [committedIndex_all_zero, committedIndex_all_zero]
  simp

/-- **JCI9** — Empty `incoming` gives joint committed index 0.

    **Model divergence from Rust**: in the Rust implementation, an empty config's
    `committed_index` returns `u64::MAX`, so `min(ci_in, MAX) = ci_in` for
    a non-joint configuration.  In this model `committedIndex [] _ = 0`, so
    the joint result degenerates to `min(0, ci_out) = 0`, not `ci_in`.
    See `CORRESPONDENCE.md` for the full analysis. -/
theorem jointCommittedIndex_empty_in (outgoing : List Nat) (acked : AckedFn) :
    jointCommittedIndex [] outgoing acked = 0 := by
  unfold jointCommittedIndex
  rw [committedIndex_empty]
  simp

/-- **JCI10** — Empty `outgoing` gives joint committed index 0.

    Same model divergence as JCI9: `committedIndex [] _ = 0`, so
    `min(ci_in, 0) = 0`.  In Rust, an empty outgoing gives the full
    `ci_in` (since `min(ci_in, MAX) = ci_in`). -/
theorem jointCommittedIndex_empty_out (incoming : List Nat) (acked : AckedFn) :
    jointCommittedIndex incoming [] acked = 0 := by
  unfold jointCommittedIndex
  rw [committedIndex_empty]
  simp

end FVSquad.JointCommittedIndex
