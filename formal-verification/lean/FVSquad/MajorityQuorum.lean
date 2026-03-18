/-!
# Majority Quorum — Lean 4 Specification

Formal specification of the `majority` utility function and `MajorityConfig::vote_result`
from `raft-rs` (`src/util.rs` and `src/quorum/majority.rs`).

## Model scope and approximations

* **Types**: Voter IDs are modelled as `Nat` (the Rust type is `u64`; we ignore the 64-bit
  bound since the properties of interest are algebraic, not overflow-sensitive).
* **`majority`**: modelled exactly — it is a pure arithmetic function.
* **`vote_result`**: modelled over a finite multiset/list of votes; Rust's `HashSet` is
  modelled as a `Finset Nat` (no duplicate IDs, no hash-map concerns).
* **Omitted**: concurrency, I/O, error handling, memory layout, and Rust's `AckedIndexer`
  trait (handled in `committed_index`, a separate target).

🔬 *Lean Squad — auto-generated formal specification.*

-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace FVSquad.MajorityQuorum

/-! ## VoteResult type -/

/-- The result of a majority vote, mirroring the Rust `VoteResult` enum. -/
inductive VoteResult where
  | Pending : VoteResult   -- neither won nor lost yet
  | Lost    : VoteResult   -- a quorum of "no" has been reached (i.e., "yes" cannot win)
  | Won     : VoteResult   -- a quorum of "yes" has been reached
  deriving DecidableEq, Repr

/-! ## The `majority` function -/

/-- `majority n` returns the minimum number of votes required for a strict majority
    among `n` voters. Corresponds to `(n / 2) + 1` in Rust (integer division). -/
def majority (n : Nat) : Nat := n / 2 + 1

-- Sanity checks (evaluated at compile time by the kernel)
#eval majority 0   -- 1
#eval majority 1   -- 1
#eval majority 2   -- 2
#eval majority 3   -- 2
#eval majority 4   -- 3
#eval majority 5   -- 3

/-! ## Key properties of `majority` -/

/-- `majority n` is always at least 1. -/
theorem majority_pos (n : Nat) : 1 ≤ majority n := by
  simp [majority]

/-- `majority n` is strictly greater than half of `n`. -/
theorem majority_gt_half (n : Nat) : 2 * majority n > n := by
  simp [majority]
  omega

/-- `majority n` is at most `n`, for all `n ≥ 1`. -/
theorem majority_le (n : Nat) (hn : 1 ≤ n) : majority n ≤ n := by
  simp [majority]
  omega

/-- `majority` is monotone: larger clusters have larger (or equal) quorum thresholds. -/
theorem majority_mono {m n : Nat} (h : m ≤ n) : majority m ≤ majority n := by
  simp [majority]
  omega

/-- The quorum intersection property: if two groups each have at least `majority n` members
    out of a universe of size `n`, then `2 * majority n > n`.
    (The Finset-level intersection theorem is stated separately as `quorum_intersection`.) -/
theorem quorum_intersection_arith (n : Nat) (hn : 1 ≤ n) :
    majority n + majority n > n := by
  simp [majority]
  omega

/-! ## The `vote_result` function -/

/-- A vote assignment maps each voter ID to its vote status:
    `some true` = voted yes, `some false` = voted no, `none` = not yet voted. -/
def VoteAssignment := Nat → Option Bool

/-- Count yes votes among the given voter set. -/
def yesCount (voters : Finset Nat) (check : VoteAssignment) : Nat :=
  (voters.filter (fun v => check v = some true)).card

/-- Count missing (pending) votes among the given voter set. -/
def missingCount (voters : Finset Nat) (check : VoteAssignment) : Nat :=
  (voters.filter (fun v => check v = none)).card

/-- `vote_result` — functional model of `MajorityConfig::vote_result`.
    Returns the election outcome given the current vote assignment. -/
def voteResult (voters : Finset Nat) (check : VoteAssignment) : VoteResult :=
  if voters.card = 0 then
    VoteResult.Won   -- empty config: by convention, wins
  else
    let q       := majority voters.card
    let yes     := yesCount voters check
    let missing := missingCount voters check
    if yes ≥ q then
      VoteResult.Won
    else if yes + missing ≥ q then
      VoteResult.Pending
    else
      VoteResult.Lost

/-! ## Key correctness properties of `vote_result` -/

/-- An empty voter set always returns Won. -/
theorem voteResult_empty (check : VoteAssignment) :
    voteResult ∅ check = VoteResult.Won := by
  simp [voteResult]

/-- If a quorum of yes votes has been received, the result is Won. -/
theorem voteResult_won_iff
    (voters : Finset Nat) (check : VoteAssignment) (hne : voters.card ≠ 0) :
    voteResult voters check = VoteResult.Won ↔
    yesCount voters check ≥ majority voters.card := by
  simp [voteResult, hne]
  split_ifs with h
  · constructor
    · intro; exact h
    · intro; rfl
  · constructor
    · intro heq; exact absurd h (by simp [heq])
    · intro hge; exact absurd hge (by omega)

/-- If even all missing voters voting yes cannot reach quorum, the result is Lost. -/
theorem voteResult_lost_iff
    (voters : Finset Nat) (check : VoteAssignment) (hne : voters.card ≠ 0) :
    voteResult voters check = VoteResult.Lost ↔
    yesCount voters check + missingCount voters check < majority voters.card := by
  simp [voteResult, hne]
  split_ifs with h1 h2
  · -- h1 : yes ≥ q, so yes + missing ≥ q too
    constructor
    · intro heq; exact absurd heq (by simp)
    · intro hlt; omega
  · -- ¬h1, h2 : yes + missing ≥ q
    constructor
    · intro heq; exact absurd heq (by simp)
    · intro hlt; omega
  · -- ¬h1, ¬h2
    constructor
    · intro _; omega
    · intro _; rfl

/-- The result is Pending iff the vote is genuinely uncertain (not Won, not Lost). -/
theorem voteResult_pending_iff
    (voters : Finset Nat) (check : VoteAssignment) (hne : voters.card ≠ 0) :
    voteResult voters check = VoteResult.Pending ↔
    yesCount voters check < majority voters.card ∧
    yesCount voters check + missingCount voters check ≥ majority voters.card := by
  simp [voteResult, hne]
  split_ifs with h1 h2 <;> simp_all <;> omega

/-- If Won is returned, it is impossible for the vote to also be Lost
    (non-overlapping outcomes). -/
theorem voteResult_won_not_lost
    (voters : Finset Nat) (check : VoteAssignment)
    (h : voteResult voters check = VoteResult.Won) :
    voteResult voters check ≠ VoteResult.Lost := by
  simp [h]

/-- Quorum intersection: if the vote Won under assignment `check1`, and Won under
    assignment `check2`, and both sets equal the same voter set, then:
    `yesCount voters check1 + yesCount voters check2 > voters.card`. -/
theorem quorum_intersection
    (voters : Finset Nat) (check1 check2 : VoteAssignment)
    (h1 : yesCount voters check1 ≥ majority voters.card)
    (h2 : yesCount voters check2 ≥ majority voters.card)
    (hne : voters.card ≠ 0) :
    yesCount voters check1 + yesCount voters check2 > voters.card := by
  have := majority_gt_half voters.card
  omega

end FVSquad.MajorityQuorum
