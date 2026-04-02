import FVSquad.MajorityVote

/-!
# Formal Specification: `ProgressTracker::tally_votes`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises `ProgressTracker::tally_votes` from `src/tracker.rs`.
It builds on `FVSquad.MajorityVote` (majority-quorum vote model).

## What `tally_votes` does

```rust
pub fn tally_votes(&self) -> (usize, usize, VoteResult) {
    let (mut granted, mut rejected) = (0, 0);
    for (id, vote) in &self.votes {
        if !self.conf.voters.contains(*id) { continue; }
        if *vote { granted += 1; } else { rejected += 1; }
    }
    let result = self.vote_result(&self.votes);
    (granted, rejected, result)
}
```

Counts yes-votes (`granted`) and no-votes (`rejected`) among the **current voters**,
ignoring non-voter entries in the `votes` map. Returns the triple together with
the overall `VoteResult`.

## Modelling choices

- Voters: `List Nat` (abstracts `JointConfig` — here we model the majority-quorum
  case; the joint case follows from `JointVote` composition).
- Votes: `Nat → Option Bool` (abstracts `HashMap<u64, bool>`; `None` = not yet voted).
- `u64` → `Nat`; no overflow modelled.
- Non-voter votes are abstracted away: the check function is applied only to voter IDs,
  so extra entries for non-voters are not representable and need not be modelled.
-/

/-! ## No-vote (rejected) counter -/

/-- Count voters that returned `Some false` (no-votes / rejections).
    Mirrors the `if *vote { granted += 1; } else { rejected += 1; }` false branch. -/
def noCount : List Nat → (Nat → Option Bool) → Nat
  | [],      _     => 0
  | v :: vs, check => (if check v = some false then 1 else 0) + noCount vs check

/-! ## The `tally_votes` model -/

/-- Pure functional model of `ProgressTracker::tally_votes` restricted to a majority
    quorum.  Returns `(granted, rejected, voteResult)`. -/
def tallyVotes (voters : List Nat) (check : Nat → Option Bool) :
    Nat × Nat × VoteResult :=
  (yesCount voters check, noCount voters check, voteResult voters check)

/-! ## Evaluations -/

section Eval
-- 3 voters: 2 yes → Won (2 ≥ majority 3 = 2)
#eval tallyVotes [1, 2, 3] (fun v => match v with
  | 1 => some true | 2 => some true | _ => some false)
-- expected: (2, 1, Won)

-- 3 voters: 1 yes, 1 no, 1 missing → Pending
#eval tallyVotes [1, 2, 3] (fun v => match v with
  | 1 => some true | 2 => some false | _ => none)
-- expected: (1, 1, Pending)

-- 3 voters: 2 no → Lost
#eval tallyVotes [1, 2, 3] (fun v => match v with
  | 1 => some false | 2 => some false | _ => some true)
-- expected: (1, 2, Lost)

-- Empty voters → (0, 0, Won)
#eval tallyVotes [] (fun _ => some true)
-- expected: (0, 0, Won)

-- Nobody voted yet → (0, 0, Pending)
#eval tallyVotes [1, 2, 3] (fun _ => none)
-- expected: (0, 0, Pending)
end Eval

/-! ## Auxiliary lemmas -/

section AuxLemmas

/-- noCount is bounded by voters.length. -/
theorem noCount_le_length (voters : List Nat) (check : Nat → Option Bool) :
    noCount voters check ≤ voters.length := by
  induction voters with
  | nil => simp [noCount]
  | cons v vs ih =>
    simp only [noCount, List.length_cons]
    by_cases h : check v = some false
    · simp only [if_pos h]; omega
    · simp only [if_neg h]; omega

/-- For each voter, exactly one of yes/no/missing fires. -/
theorem yes_no_missing_partition (v : Nat) (check : Nat → Option Bool) :
    (if check v = some true then 1 else 0) +
    (if check v = some false then 1 else 0) +
    (if check v = none then 1 else 0) = 1 := by
  rcases (check v) with (_ | _ | _) <;> simp

/-- yesCount + noCount + missingCount = voters.length (exact partition). -/
theorem yes_no_missing_eq_length (voters : List Nat) (check : Nat → Option Bool) :
    yesCount voters check + noCount voters check + missingCount voters check =
    voters.length := by
  induction voters with
  | nil => simp [yesCount, noCount, missingCount]
  | cons v vs ih =>
    simp only [yesCount, noCount, missingCount, List.length_cons]
    have := yes_no_missing_partition v check
    omega

/-- yesCount + noCount ≤ voters.length. -/
theorem yes_no_le_length (voters : List Nat) (check : Nat → Option Bool) :
    yesCount voters check + noCount voters check ≤ voters.length := by
  have h := yes_no_missing_eq_length voters check
  have hm := missingCount_le_length voters check
  omega

/-- For all n: n < 2 * majority n  (strict). -/
theorem lt_two_majority (n : Nat) : n < 2 * majority n := by
  simp [majority]; omega

/-- If rejected ≥ majority n, then yes + missing < majority n. -/
theorem rej_majority_implies_yes_missing_lt
    (voters : List Nat) (check : Nat → Option Bool)
    (hrej : noCount voters check ≥ majority voters.length) :
    yesCount voters check + missingCount voters check < majority voters.length := by
  have hpart := yes_no_missing_eq_length voters check
  have hlt := lt_two_majority voters.length
  omega

/-- noCount = 0 when all voters vote yes. -/
theorem noCount_all_yes (voters : List Nat) (check : Nat → Option Bool)
    (hall : ∀ v ∈ voters, check v = some true) :
    noCount voters check = 0 := by
  induction voters with
  | nil => rfl
  | cons v vs ih =>
    simp only [noCount]
    have hv : check v = some true := hall v (List.mem_cons.mpr (Or.inl rfl))
    have hne : check v ≠ some false := by rw [hv]; decide
    simp only [if_neg hne]
    have hrec := ih (fun w hw => hall w (List.mem_cons.mpr (Or.inr hw)))
    omega

/-- yesCount = 0 when all voters vote no. -/
theorem yesCount_all_no (voters : List Nat) (check : Nat → Option Bool)
    (hall : ∀ v ∈ voters, check v = some false) :
    yesCount voters check = 0 := by
  induction voters with
  | nil => rfl
  | cons v vs ih =>
    simp only [yesCount]
    have hv : check v = some false := hall v (List.mem_cons.mpr (Or.inl rfl))
    have hne : check v ≠ some true := by rw [hv]; decide
    simp only [if_neg hne]
    have hrec := ih (fun w hw => hall w (List.mem_cons.mpr (Or.inr hw)))
    omega

/-- noCount = voters.length when all voters vote no. -/
theorem noCount_all_no (voters : List Nat) (check : Nat → Option Bool)
    (hall : ∀ v ∈ voters, check v = some false) :
    noCount voters check = voters.length := by
  induction voters with
  | nil => rfl
  | cons v vs ih =>
    simp only [noCount, List.length_cons]
    have hv : check v = some false := hall v (List.mem_cons.mpr (Or.inl rfl))
    simp only [if_pos hv]
    have hrec := ih (fun w hw => hall w (List.mem_cons.mpr (Or.inr hw)))
    omega

/-- missingCount = 0 when all voters vote no. -/
theorem missingCount_all_no (voters : List Nat) (check : Nat → Option Bool)
    (hall : ∀ v ∈ voters, check v = some false) :
    missingCount voters check = 0 := by
  induction voters with
  | nil => rfl
  | cons v vs ih =>
    simp only [missingCount]
    have hv : check v = some false := hall v (List.mem_cons.mpr (Or.inl rfl))
    have hne : check v ≠ none := by rw [hv]; decide
    simp only [if_neg hne]
    have hrec := ih (fun w hw => hall w (List.mem_cons.mpr (Or.inr hw)))
    omega

end AuxLemmas

/-! ## Component projection lemmas -/

section Projections

/-- TV1: Granted (first component) equals yesCount. -/
theorem tallyVotes_granted_eq (voters : List Nat) (check : Nat → Option Bool) :
    (tallyVotes voters check).1 = yesCount voters check := rfl

/-- TV2: Rejected (second component) equals noCount. -/
theorem tallyVotes_rejected_eq (voters : List Nat) (check : Nat → Option Bool) :
    (tallyVotes voters check).2.1 = noCount voters check := rfl

/-- TV3: Result (third component) equals voteResult. -/
theorem tallyVotes_result_eq (voters : List Nat) (check : Nat → Option Bool) :
    (tallyVotes voters check).2.2 = voteResult voters check := rfl

end Projections

/-! ## Key theorems -/

/-- TV4: granted ≤ voters.length. -/
theorem tallyVotes_granted_le (voters : List Nat) (check : Nat → Option Bool) :
    (tallyVotes voters check).1 ≤ voters.length :=
  yesCount_le_length voters check

/-- TV5: rejected ≤ voters.length. -/
theorem tallyVotes_rejected_le (voters : List Nat) (check : Nat → Option Bool) :
    (tallyVotes voters check).2.1 ≤ voters.length :=
  noCount_le_length voters check

/-- TV6: granted + rejected ≤ voters.length. -/
theorem tallyVotes_granted_add_rejected_le (voters : List Nat) (check : Nat → Option Bool) :
    (tallyVotes voters check).1 + (tallyVotes voters check).2.1 ≤ voters.length :=
  yes_no_le_length voters check

/-- TV7: Exact partition: granted + rejected + missing = voters.length. -/
theorem tallyVotes_partition (voters : List Nat) (check : Nat → Option Bool) :
    (tallyVotes voters check).1 + (tallyVotes voters check).2.1 +
    missingCount voters check = voters.length :=
  yes_no_missing_eq_length voters check

/-- TV8: Empty voters → (0, 0, Won). -/
theorem tallyVotes_empty (check : Nat → Option Bool) :
    tallyVotes [] check = (0, 0, VoteResult.Won) := rfl

/-- TV9: Result is Won iff granted ≥ majority(n) (non-empty voters). -/
theorem tallyVotes_won_iff (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ []) :
    (tallyVotes voters check).2.2 = VoteResult.Won ↔
    (tallyVotes voters check).1 ≥ majority voters.length :=
  voteResult_Won_iff voters check hne

/-- TV10: Result is Lost iff granted + missing < majority(n) (non-empty). -/
theorem tallyVotes_lost_iff (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ []) :
    (tallyVotes voters check).2.2 = VoteResult.Lost ↔
    (tallyVotes voters check).1 + missingCount voters check < majority voters.length :=
  voteResult_Lost_iff voters check hne

/-- TV11: Won when granted ≥ majority. -/
theorem tallyVotes_won_of_granted_ge (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ [])
    (hg : (tallyVotes voters check).1 ≥ majority voters.length) :
    (tallyVotes voters check).2.2 = VoteResult.Won :=
  (tallyVotes_won_iff voters check hne).mpr hg

/-- TV12: Lost when rejected ≥ majority (the "rejection closes the election" theorem).

    This is the key safety property: if a majority of voters have actively rejected
    the candidate, no amount of future yes-votes can form a quorum, so the election
    is definitively lost. -/
theorem tallyVotes_lost_of_rejected_ge (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ [])
    (hrej : (tallyVotes voters check).2.1 ≥ majority voters.length) :
    (tallyVotes voters check).2.2 = VoteResult.Lost := by
  rw [tallyVotes_lost_iff voters check hne]
  exact rej_majority_implies_yes_missing_lt voters check hrej

/-- TV13: Result is exhaustive (one of Won / Pending / Lost). -/
theorem tallyVotes_result_exhaustive (voters : List Nat) (check : Nat → Option Bool) :
    (tallyVotes voters check).2.2 = VoteResult.Won ∨
    (tallyVotes voters check).2.2 = VoteResult.Pending ∨
    (tallyVotes voters check).2.2 = VoteResult.Lost :=
  voteResult_exhaustive voters check

/-- TV14: granted + rejected > 0 when at least one voter has voted. -/
theorem tallyVotes_voted_positive (voters : List Nat) (check : Nat → Option Bool)
    (v : Nat) (hmem : v ∈ voters) (hvote : check v ≠ none) :
    (tallyVotes voters check).1 + (tallyVotes voters check).2.1 > 0 := by
  simp only [tallyVotes]
  induction voters with
  | nil => simp at hmem
  | cons w ws ih =>
    simp only [yesCount, noCount, List.mem_cons] at *
    rcases hmem with rfl | hmem'
    · -- v = w: this voter has voted
      cases h2 : check v with
      | none => exact absurd h2 hvote
      | some b =>
        cases b
        · simp; omega
        · simp; omega
    · -- v ∈ ws
      have := ih hmem'
      omega

/-- TV15: All-yes → (|voters|, 0, Won). -/
theorem tallyVotes_all_yes (voters : List Nat) (check : Nat → Option Bool)
    (hall : ∀ v ∈ voters, check v = some true) :
    tallyVotes voters check = (voters.length, 0, VoteResult.Won) := by
  simp only [tallyVotes,
    yesCount_all_yes voters check hall,
    noCount_all_yes voters check hall,
    voteResult_all_yes voters check hall]

/-- TV16: All-no → (0, |voters|, Lost) for non-empty voters. -/
theorem tallyVotes_all_no (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ [])
    (hall : ∀ v ∈ voters, check v = some false) :
    tallyVotes voters check = (0, voters.length, VoteResult.Lost) := by
  have hlost : voteResult voters check = VoteResult.Lost := by
    rw [voteResult_Lost_iff voters check hne]
    rw [yesCount_all_no voters check hall, missingCount_all_no voters check hall]
    exact majority_pos voters.length
  simp only [tallyVotes,
    yesCount_all_no voters check hall,
    noCount_all_no voters check hall,
    hlost]

/-- TV17: Pending iff both granted < majority and granted+missing ≥ majority. -/
theorem tallyVotes_pending_iff (voters : List Nat) (check : Nat → Option Bool)
    (hne : voters ≠ []) :
    (tallyVotes voters check).2.2 = VoteResult.Pending ↔
    (tallyVotes voters check).1 < majority voters.length ∧
    (tallyVotes voters check).1 + missingCount voters check ≥ majority voters.length :=
  voteResult_Pending_iff voters check hne

/-- TV18: No double-quorum: Won and Lost cannot hold simultaneously. -/
theorem tallyVotes_no_double_quorum (voters : List Nat) (check : Nat → Option Bool) :
    ¬ ((tallyVotes voters check).2.2 = VoteResult.Won ∧
       (tallyVotes voters check).2.2 = VoteResult.Lost) := by
  intro ⟨hw, hl⟩
  rw [hw] at hl
  exact absurd hl (by decide)
