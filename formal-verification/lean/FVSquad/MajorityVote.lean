/-!
# Formal Specification: `Configuration::vote_result`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises `Configuration::vote_result` from `src/quorum/majority.rs`.

## What `vote_result` does

```rust
pub fn vote_result(&self, check: impl Fn(u64) -> Option<bool>) -> VoteResult
```

Given a majority quorum configuration and a check function, determines whether
the quorum has `Won`, is `Pending`, or has `Lost`.

Algorithm:
1. Empty voters → `Won` (convention for joint quorum compatibility).
2. Count `yes` (`Some(true)`) and `missing` (`None`) votes.
3. `q = majority(n) = n/2 + 1`.
4. `Won` if `yes ≥ q`; `Pending` if `yes + missing ≥ q`; else `Lost`.

## Modelling choices

- `HashSet<u64>` voters → `List Nat` (uniqueness assumed where noted).
- `impl Fn(u64) → Option<bool>` → `Nat → Option Bool`.
- Recursive definitions (not `foldl`) for easy structural induction.
- `u64` → `Nat`; no overflow modelled.
-/

/-! ## VoteResult type -/

/-- Three-valued vote outcome. Mirrors `VoteResult` in `src/quorum.rs`. -/
inductive VoteResult where
  | Pending | Lost | Won
  deriving DecidableEq, Repr

/-! ## Majority quorum threshold -/

/-- Minimum yes-votes needed to win an `n`-voter quorum.
    Mirrors `majority` in `src/util.rs:123`. -/
def majority (n : Nat) : Nat := n / 2 + 1

/-! ## Vote counting helpers -/

/-- Count voters that returned `Some true` (yes votes). -/
def yesCount : List Nat → (Nat → Option Bool) → Nat
  | [],      _     => 0
  | v :: vs, check => (if check v = some true then 1 else 0) + yesCount vs check

/-- Count voters that returned `None` (not yet voted). -/
def missingCount : List Nat → (Nat → Option Bool) → Nat
  | [],      _     => 0
  | v :: vs, check => (if check v = none then 1 else 0) + missingCount vs check

/-! ## The pure functional model -/

/-- Determines the vote result for a majority quorum.
    Mirrors `Configuration::vote_result` in `src/quorum/majority.rs:189`. -/
def voteResult (voters : List Nat) (check : Nat → Option Bool) : VoteResult :=
  match voters with
  | [] => VoteResult.Won
  | _  =>
    let yes     := yesCount voters check
    let missing := missingCount voters check
    let q       := majority voters.length
    if yes ≥ q then VoteResult.Won
    else if yes + missing ≥ q then VoteResult.Pending
    else VoteResult.Lost

/-! ## Evaluations -/

section Eval
#eval voteResult [1, 2, 3] (fun v => match v with
  | 1 => some true | 2 => some true | _ => some false)   -- Won
#eval voteResult [1, 2, 3] (fun v => match v with
  | 1 => some true | 2 => none | _ => some false)         -- Pending
#eval voteResult [1, 2, 3] (fun v => match v with
  | 3 => some true | _ => some false)                     -- Lost
#eval voteResult [] (fun _ => none)                        -- Won (empty)
end Eval

/-! ## Auxiliary lemmas -/

section Lemmas

@[simp] theorem majority_zero : majority 0 = 1 := rfl

theorem majority_pos (n : Nat) : 0 < majority n := by simp [majority]

theorem majority_gt_half (n : Nat) : n / 2 < majority n := by simp [majority]

theorem yesCount_le_length (voters : List Nat) (check : Nat → Option Bool) :
    yesCount voters check ≤ voters.length := by
  induction voters with
  | nil => simp [yesCount]
  | cons v vs ih =>
    simp only [yesCount, List.length_cons]
    by_cases h : check v = some true
    · simp only [if_pos h]; omega
    · simp only [if_neg h]; omega

theorem missingCount_le_length (voters : List Nat) (check : Nat → Option Bool) :
    missingCount voters check ≤ voters.length := by
  induction voters with
  | nil => simp [missingCount]
  | cons v vs ih =>
    simp only [missingCount, List.length_cons]
    by_cases h : check v = none
    · simp only [if_pos h]; omega
    · simp only [if_neg h]; omega

theorem yesCount_add_missing_le (voters : List Nat) (check : Nat → Option Bool) :
    yesCount voters check + missingCount voters check ≤ voters.length := by
  induction voters with
  | nil => simp [yesCount, missingCount]
  | cons v vs ih =>
    simp only [yesCount, missingCount, List.length_cons]
    by_cases h1 : check v = some true
    · by_cases h2 : check v = none
      · simp [h1] at h2  -- some true ≠ none
      · simp only [if_pos h1, if_neg h2]; omega
    · by_cases h2 : check v = none
      · simp only [if_neg h1, if_pos h2]; omega
      · simp only [if_neg h1, if_neg h2]; omega

/-- All-yes count equals length. -/
theorem yesCount_all_yes (voters : List Nat) (check : Nat → Option Bool)
    (hall : ∀ v ∈ voters, check v = some true) :
    yesCount voters check = voters.length := by
  induction voters with
  | nil => rfl
  | cons v vs ih =>
    simp only [yesCount, List.length_cons]
    have hv : check v = some true := hall v List.mem_cons_self
    simp only [if_pos hv]
    have ih' := ih (fun w hw => hall w (List.Mem.tail v hw))
    omega

end Lemmas

/-! ## Key theorems -/

/-- M1: Empty voters always yields Won (joint-quorum convention). -/
theorem voteResult_empty_is_Won (check : Nat → Option Bool) :
    voteResult [] check = VoteResult.Won := rfl

/-- M2: The majority threshold is always positive. -/
theorem majority_always_pos (n : Nat) : 0 < majority n := majority_pos n

/-- M3: The majority threshold strictly exceeds half. -/
theorem majority_exceeds_half (n : Nat) : n / 2 < majority n := majority_gt_half n

/-- M4: majority is monotone. -/
theorem majority_monotone {m n : Nat} (h : m ≤ n) : majority m ≤ majority n := by
  simp [majority]; omega

/-- V1: Won iff yes-count ≥ majority (for non-empty voters). -/
theorem voteResult_Won_iff (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ []) :
    voteResult voters check = VoteResult.Won ↔
    yesCount voters check ≥ majority voters.length := by
  cases voters with
  | nil => exact absurd rfl hne
  | cons v vs =>
    simp only [voteResult, List.length_cons]
    constructor
    · intro h
      by_cases hge : yesCount (v :: vs) check ≥ majority (vs.length + 1)
      · exact hge
      · simp only [if_neg hge] at h
        by_cases hpend : yesCount (v :: vs) check + missingCount (v :: vs) check ≥
            majority (vs.length + 1)
        · simp only [if_pos hpend] at h; exact absurd h (by decide)
        · simp only [if_neg hpend] at h; exact absurd h (by decide)
    · intro hge
      simp only [if_pos hge]

/-- M5: A single voter that votes yes achieves a majority. -/
theorem single_yes_wins (v : Nat) (check : Nat → Option Bool)
    (h : check v = some true) :
    voteResult [v] check = VoteResult.Won := by
  rw [voteResult_Won_iff [v] check (List.cons_ne_nil v [])]
  simp [yesCount, h, majority]

/-- V2: Lost iff yes+missing < majority (for non-empty voters). -/
theorem voteResult_Lost_iff (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ []) :
    voteResult voters check = VoteResult.Lost ↔
    yesCount voters check + missingCount voters check < majority voters.length := by
  cases voters with
  | nil => exact absurd rfl hne
  | cons v vs =>
    simp only [voteResult, List.length_cons]
    constructor
    · intro h
      by_cases hge : yesCount (v :: vs) check ≥ majority (vs.length + 1)
      · simp only [if_pos hge] at h; exact absurd h (by decide)
      · simp only [if_neg hge] at h
        by_cases hpend : yesCount (v :: vs) check + missingCount (v :: vs) check ≥
            majority (vs.length + 1)
        · simp only [if_pos hpend] at h; exact absurd h (by decide)
        · omega
    · intro hlt
      have hge : ¬ yesCount (v :: vs) check ≥ majority (vs.length + 1) := by omega
      have hpend : ¬ yesCount (v :: vs) check + missingCount (v :: vs) check ≥
          majority (vs.length + 1) := by omega
      simp only [if_neg hge, if_neg hpend]

/-- V3: Pending iff yes < majority but yes+missing ≥ majority. -/
theorem voteResult_Pending_iff (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ []) :
    voteResult voters check = VoteResult.Pending ↔
    yesCount voters check < majority voters.length ∧
    yesCount voters check + missingCount voters check ≥ majority voters.length := by
  cases voters with
  | nil => exact absurd rfl hne
  | cons v vs =>
    simp only [voteResult, List.length_cons]
    constructor
    · intro h
      by_cases hge : yesCount (v :: vs) check ≥ majority (vs.length + 1)
      · simp only [if_pos hge] at h; exact absurd h (by decide)
      · simp only [if_neg hge] at h
        by_cases hpend : yesCount (v :: vs) check + missingCount (v :: vs) check ≥
            majority (vs.length + 1)
        · simp only [if_pos hpend] at h
          exact ⟨by omega, hpend⟩
        · simp only [if_neg hpend] at h; exact absurd h (by decide)
    · intro ⟨hlt, hpend⟩
      have hge : ¬ yesCount (v :: vs) check ≥ majority (vs.length + 1) := by omega
      simp only [if_neg hge, if_pos hpend]

/-- V4: If all voters vote yes, the result is Won. -/
theorem voteResult_all_yes (voters : List Nat) (check : Nat → Option Bool)
    (hall : ∀ v ∈ voters, check v = some true) :
    voteResult voters check = VoteResult.Won := by
  cases voters with
  | nil => rfl
  | cons v vs =>
    rw [voteResult_Won_iff (v :: vs) check (List.cons_ne_nil v vs)]
    simp only [List.length_cons]
    have hlen := yesCount_all_yes (v :: vs) check hall
    simp only [List.length_cons] at hlen
    -- yesCount = vs.length + 1, majority(vs.length+1) ≤ vs.length + 1
    have hmaj : majority (vs.length + 1) ≤ vs.length + 1 := by
      simp [majority]; omega
    omega

/-- V5: Result is one of Won, Pending, or Lost. -/
theorem voteResult_exhaustive (voters : List Nat) (check : Nat → Option Bool) :
    voteResult voters check = VoteResult.Won ∨
    voteResult voters check = VoteResult.Pending ∨
    voteResult voters check = VoteResult.Lost := by
  cases voters with
  | nil => exact Or.inl rfl
  | cons v vs =>
    simp only [voteResult]
    by_cases h1 : yesCount (v :: vs) check ≥ majority (v :: vs).length
    · exact Or.inl (if_pos h1)
    · simp only [if_neg h1]
      by_cases h2 : yesCount (v :: vs) check + missingCount (v :: vs) check ≥
          majority (v :: vs).length
      · exact Or.inr (Or.inl (if_pos h2))
      · exact Or.inr (Or.inr (if_neg h2))

/-- V6: Non-empty: not Won when yes < majority. -/
theorem voteResult_not_Won_of_few_yes (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ [])
    (hlt : yesCount voters check < majority voters.length) :
    voteResult voters check ≠ VoteResult.Won := by
  intro hw
  rw [voteResult_Won_iff voters check hne] at hw
  omega

/-- V7: Non-empty: not Lost when yes+missing ≥ majority. -/
theorem voteResult_not_Lost_of_optimistic (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ [])
    (hge : yesCount voters check + missingCount voters check ≥ majority voters.length) :
    voteResult voters check ≠ VoteResult.Lost := by
  intro hl
  rw [voteResult_Lost_iff voters check hne] at hl
  omega

/-- V8: Won when yes ≥ majority (convenience form of V1). -/
theorem voteResult_majority_yes_wins (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ [])
    (hyes : yesCount voters check ≥ majority voters.length) :
    voteResult voters check = VoteResult.Won :=
  (voteResult_Won_iff voters check hne).mpr hyes

/-- V9: yesCount + missingCount ≤ voters.length (count bound). -/
theorem voteResult_count_bound (voters : List Nat) (check : Nat → Option Bool) :
    yesCount voters check + missingCount voters check ≤ voters.length :=
  yesCount_add_missing_le voters check

/-- V10: yesCount ≤ voters.length. -/
theorem voteResult_yes_bound (voters : List Nat) (check : Nat → Option Bool) :
    yesCount voters check ≤ voters.length :=
  yesCount_le_length voters check
