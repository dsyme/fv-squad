import FVSquad.MajorityVote

/-!
# CommittedIndex — Lean 4 Specification and Implementation Model

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Formal specification and implementation model of
`Configuration::committed_index` from `src/quorum/majority.rs`
(non-group-commit path).  This is one of the most safety-critical
computations in Raft: it determines the largest log index that has
been acknowledged by a majority of voters and may therefore be safely
committed.

## Algorithm

1. Collect `acked_index(v)` for every voter `v` (defaulting unknown to `0`).
2. Sort the collected indices in **descending** order.
3. Return the element at position `majority(n) − 1` (0-indexed), where
   `majority(n) = n / 2 + 1`.

Example: acked indices `[2, 2, 2, 4, 5]` sorted desc = `[5, 4, 2, 2, 2]`;
`majority(5) = 3`; result = `sorted[2] = 2`.

## Model scope and approximations

* **Non-group-commit path only**: the `use_group_commit = true` branch is not
  modelled here (requires extra group-ID bookkeeping).
* **Types**: voter IDs are `Nat` (Rust: `u64`).  Acked log indices are `Nat`.
* **`AckedFn`**: models `impl AckedIndexer` as a pure `Nat → Nat` function;
  `None` (unknown voters) is mapped to `0` via Rust's `unwrap_or_default()`.
* **Empty-config return value**: Rust returns `u64::MAX` so that
  `min(empty_result, other) = other` in joint quorums.  This model returns `0`
  to stay in `Nat`; the divergence is captured in `committedIndex_empty_contract`.
* **Voter list vs. set**: Rust uses a `HashSet<u64>`; this model uses `List Nat`
  (duplicates assumed absent where it matters).
* **Stack/heap allocation**: the Rust unsafe stack-array optimisation is a
  performance detail only; this model uses `List` throughout.
* **Omitted**: group-commit extension, concurrency, I/O, `AckedIndexer` trait
  dispatch, Rust `u64` overflow semantics, memory layout.
-/

namespace FVSquad.CommittedIndex

/-! ## Core types and helpers -/

/-- Models `impl AckedIndexer`: a pure function from voter ID to acknowledged index.
    `None` results in Rust are mapped to `0` via `unwrap_or_default()`. -/
abbrev AckedFn := Nat → Nat

/-- Sort a list of natural numbers in **descending** order.
    Mirrors the `matched.sort_by(|a, b| b.index.cmp(&a.index))` call in Rust. -/
def sortDesc (l : List Nat) : List Nat :=
  l.mergeSort (fun a b => decide (a ≥ b))

/-- `sortDesc` preserves the length. -/
theorem sortDesc_length (l : List Nat) : (sortDesc l).length = l.length :=
  List.length_mergeSort l

/-- `sortDesc` is a permutation of the input. -/
theorem sortDesc_perm (l : List Nat) : (sortDesc l).Perm l :=
  List.mergeSort_perm l (fun a b => decide (a ≥ b))

/-- The `(· ≥ ·)` predicate used by `sortDesc` is transitive. -/
private theorem ge_trans' (a b c : Nat) (h1 : decide (a ≥ b) = true) (h2 : decide (b ≥ c) = true) :
    decide (a ≥ c) = true := by
  simp [decide_eq_true_eq] at *; omega

/-- The `(· ≥ ·)` predicate used by `sortDesc` is total. -/
private theorem ge_total' (a b : Nat) : (decide (a ≥ b) || decide (b ≥ a)) = true := by
  simp [Bool.or_eq_true, decide_eq_true_eq]; omega

/-- `sortDesc` produces a **descending** (non-increasing) list. -/
theorem sortDesc_pairwise (l : List Nat) :
    (sortDesc l).Pairwise (fun a b => decide (a ≥ b) = true) :=
  List.pairwise_mergeSort ge_trans' ge_total' l

/-- The acked indices for all voters, sorted descending. -/
def sortedAcked (voters : List Nat) (acked : AckedFn) : List Nat :=
  sortDesc (voters.map acked)

/-- Length of `sortedAcked` equals the voter count. -/
theorem sortedAcked_length (voters : List Nat) (acked : AckedFn) :
    (sortedAcked voters acked).length = voters.length := by
  simp [sortedAcked, sortDesc_length, List.length_map]

/-! ## Implementation model: `committedIndex` -/

/-- **Implementation model** of `Configuration::committed_index` (non-group-commit path).

    For non-empty voter sets: sorts all acked indices descending and returns
    the element at position `majority(n) - 1` (0-indexed).

    For the empty voter set: returns `0`.  **This diverges from Rust** (which
    returns `u64::MAX` as a sentinel for joint quorums); see
    `committedIndex_empty_contract` below. -/
def committedIndex (voters : List Nat) (acked : AckedFn) : Nat :=
  (sortedAcked voters acked).getD (majority voters.length - 1) 0

/-! ## Declarative characterisation via `countGe`

    An equivalent characterisation of `committedIndex` is:
    `committedIndex = max { k | countGe voters acked k ≥ majority(n) }`.
    This form is more convenient for stating safety and maximality. -/

/-- Number of voters whose acked index is **at least** `k`. -/
def countGe (voters : List Nat) (acked : AckedFn) (k : Nat) : Nat :=
  (voters.filter (fun v => decide (k ≤ acked v))).length

/-! ## Evaluations -/

section Eval
-- Five voters with acked indices [5,3,3,2,2]; majority(5)=3; result=3.
#eval committedIndex [1,2,3,4,5] (fun v => match v with
  | 1 => 5 | 2 => 3 | 3 => 3 | 4 => 2 | _ => 2)  -- expected 3

-- Three voters with acked indices [2,2,2]; majority(3)=2; result=2.
#eval committedIndex [1,2,3] (fun _ => 2)             -- expected 2

-- Single voter with acked index 7; result=7.
#eval committedIndex [1] (fun _ => 7)                 -- expected 7

-- Empty config; result=0 (Rust returns u64::MAX).
#eval committedIndex [] (fun _ => 42)                 -- expected 0
end Eval

/-! ## Proved theorems -/

/-- **CI1** — Empty configuration returns `0`. -/
theorem committedIndex_empty (acked : AckedFn) : committedIndex [] acked = 0 := by
  simp [committedIndex, sortedAcked, sortDesc, majority]

/-- **CI1-contract** — Documents the divergence from Rust's `u64::MAX` sentinel.
    Proofs involving joint quorums should use `min(committedIndex ..., ...)` and
    treat the empty case separately, corresponding to Rust's `min(u64::MAX, x) = x`. -/
theorem committedIndex_empty_contract (acked : AckedFn) :
    committedIndex [] acked = 0 := committedIndex_empty acked

/-- **CI2** — Single voter returns that voter's acked index. -/
theorem committedIndex_singleton (v : Nat) (acked : AckedFn) :
    committedIndex [v] acked = acked v := by
  simp [committedIndex, sortedAcked, sortDesc, majority]

/-- **CI3** — `countGe voters acked 0 = voters.length` (all natural numbers are ≥ 0). -/
theorem countGe_zero (voters : List Nat) (acked : AckedFn) :
    countGe voters acked 0 = voters.length := by
  simp [countGe]

/-- **CI4** — Antitone: raising the threshold `k` cannot increase `countGe`. -/
theorem filter_ge_sublist (voters : List Nat) (acked : AckedFn) (j k : Nat) (hjk : j ≤ k) :
    (voters.filter (fun v => decide (k ≤ acked v))).Sublist
    (voters.filter (fun v => decide (j ≤ acked v))) := by
  induction voters with
  | nil => simp
  | cons v vs ih =>
    simp only [List.filter]
    by_cases hk : decide (k ≤ acked v) = true
    · have hj : decide (j ≤ acked v) = true := by
        simp [decide_eq_true_eq] at hk ⊢; omega
      simp only [hk, hj]
      exact List.Sublist.cons₂ v ih
    · simp only [Bool.not_eq_true] at hk
      simp only [hk]
      by_cases hj : decide (j ≤ acked v) = true
      · simp only [hj]; exact List.Sublist.cons v ih
      · simp only [Bool.not_eq_true] at hj
        simp only [hj]; exact ih

theorem countGe_antitone (voters : List Nat) (acked : AckedFn) (j k : Nat) (hjk : j ≤ k) :
    countGe voters acked k ≤ countGe voters acked j :=
  List.Sublist.length_le (filter_ge_sublist voters acked j k hjk)

/-- **CI5** — `countGe` is preserved by voter list permutations. -/
theorem countGe_perm (voters1 voters2 : List Nat) (acked : AckedFn) (k : Nat)
    (hperm : voters1.Perm voters2) :
    countGe voters1 acked k = countGe voters2 acked k := by
  simp only [countGe]
  exact List.Perm.length_eq (hperm.filter _)

/-- **CI6** — `sortedAcked` is a permutation of `voters.map acked`. -/
theorem sortedAcked_perm (voters : List Nat) (acked : AckedFn) :
    (sortedAcked voters acked).Perm (voters.map acked) :=
  sortDesc_perm _

/-- **CI7** — `countGe` equals the count of elements ≥ `k` in the mapped acked list.
    Key bridge: filtering voters by `acked v ≥ k` gives the same count as
    filtering mapped values by `x ≥ k`. -/
theorem countGe_eq_countGeList (voters : List Nat) (acked : AckedFn) (k : Nat) :
    countGe voters acked k =
    ((voters.map acked).filter (fun x => decide (k ≤ x))).length := by
  simp only [countGe, List.filter_map, List.length_map]
  rfl

/-! ## Helper lemmas for order-statistic proofs -/

-- getD returns the element when the index is in bounds
private theorem getD_eq_get_of_lt (l : List Nat) (i : Nat) (h : i < l.length) :
    l.getD i 0 = l.get ⟨i, h⟩ := by
  induction l generalizing i with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.getD_eq_getElem?_getD, List.get_cons_succ]
      exact ih i' (Nat.lt_of_succ_lt_succ h)

-- getD of a list whose elements are all 0 returns 0
private theorem getD_all_zero (l : List Nat) (k : Nat) (hall : ∀ x ∈ l, x = 0) :
    l.getD k 0 = 0 := by
  induction l generalizing k with
  | nil => simp [List.getD_eq_getElem?_getD]
  | cons x xs ih =>
    cases k with
    | zero =>
      simp [List.getD_eq_getElem?_getD]
      exact hall x List.mem_cons_self
    | succ k' =>
      simp [List.getD_eq_getElem?_getD]
      exact ih k' (fun y hy => hall y (List.mem_cons_of_mem x hy))

-- pairwise (· ≥ ·) is antitone: larger index ↦ smaller or equal value
private theorem pairwise_ge_antitone (l : List Nat) (hw : l.Pairwise (· ≥ ·))
    (i j : Nat) (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l.get ⟨j, hj⟩ ≤ l.get ⟨i, hi⟩ := by
  induction l generalizing i j with
  | nil => exact absurd hi (by simp)
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
        simp only [List.get_cons_succ]
        exact (List.pairwise_cons.mp hw).1 _ (List.get_mem xs ⟨j', hj'⟩)
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.get_cons_succ]
        exact ih (List.pairwise_cons.mp hw).2 i' j'
          (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) (by omega)

-- sortDesc is antitone: smaller index ↦ larger or equal element
private theorem sortDesc_get_antitone (l : List Nat)
    (i j : Nat) (hi : i < (sortDesc l).length) (hj : j < (sortDesc l).length) (hij : i ≤ j) :
    (sortDesc l).get ⟨j, hj⟩ ≤ (sortDesc l).get ⟨i, hi⟩ := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hij'
  · exact Nat.le_refl _
  · exact pairwise_ge_antitone (sortDesc l)
      (sortDesc_pairwise l |>.imp (by intro a b h; simp [decide_eq_true_eq] at h; exact h))
      i j hi hj hij'

-- Filter (≥ v) count ≥ q if the first q elements all are ≥ v
private theorem filter_ge_prefix (l : List Nat) (v q : Nat)
    (hlen : q ≤ l.length)
    (hpre : ∀ i (hi : i < l.length), i < q → v ≤ l.get ⟨i, hi⟩) :
    q ≤ (l.filter (fun x => decide (v ≤ x))).length := by
  induction l generalizing q with
  | nil => simp at hlen; omega
  | cons x xs ih =>
    cases q with
    | zero => omega
    | succ q' =>
      have hlen' : q' ≤ xs.length := by simpa using hlen
      have hxv : v ≤ x := by
        have := hpre 0 (by simp) (Nat.zero_lt_succ q'); simpa using this
      simp only [List.filter, decide_eq_true_eq.mpr hxv, List.length_cons]
      apply Nat.succ_le_succ; apply ih; · exact hlen'
      intro i hi hiq'
      have := hpre (i+1) (by simpa using hi) (by omega)
      simpa [List.get_cons_succ] using this

-- Filter (≥ v) count ≤ q if all elements from position q onwards are < v
private theorem filter_ge_suffix (l : List Nat) (v q : Nat)
    (hsuf : ∀ i (hi : i < l.length), q ≤ i → l.get ⟨i, hi⟩ < v) :
    (l.filter (fun x => decide (v ≤ x))).length ≤ q := by
  induction l generalizing q with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter]
    by_cases hxv : v ≤ x
    · rw [decide_eq_true_eq.mpr hxv, List.length_cons]
      cases q with
      | zero =>
        have : x < v := by
          have := hsuf 0 (by simp) (Nat.le_refl 0); simpa using this
        omega
      | succ q' =>
        apply Nat.succ_le_succ; apply ih
        intro i hi hiq'
        have := hsuf (i+1) (by simpa using hi) (by omega)
        simpa [List.get_cons_succ] using this
    · rw [decide_eq_false_iff_not.mpr (Nat.not_le.mpr (Nat.lt_of_not_le hxv))]
      cases q with
      | zero =>
        apply ih; intro i hi _
        have := hsuf (i+1) (by simpa using hi) (Nat.zero_le _)
        simpa [List.get_cons_succ] using this
      | succ q' =>
        apply Nat.le_succ_of_le; apply ih
        intro i hi hiq'
        have := hsuf (i+1) (by simpa using hi) (by omega)
        simpa [List.get_cons_succ] using this

-- Permutation preserves filter length
private theorem perm_filter_length (l1 l2 : List Nat) (p : Nat → Bool) (h : l1.Perm l2) :
    (l1.filter p).length = (l2.filter p).length := (h.filter p).length_eq

-- countGe equals the filter count on the sorted acked list
private theorem countGe_eq_sa_filter (voters : List Nat) (acked : AckedFn) (k : Nat) :
    countGe voters acked k =
    ((sortedAcked voters acked).filter (fun x => decide (k ≤ x))).length := by
  rw [countGe_eq_countGeList]
  exact perm_filter_length _ _ _ (sortedAcked_perm voters acked).symm

-- countGe is monotone in the acked function (pointwise order)
private theorem countGe_mono_acked (voters : List Nat) (acked1 acked2 : AckedFn) (k : Nat)
    (hle : ∀ v, acked1 v ≤ acked2 v) :
    countGe voters acked1 k ≤ countGe voters acked2 k := by
  simp only [countGe]; apply List.Sublist.length_le
  induction voters with
  | nil => exact List.Sublist.slnil
  | cons v vs ih =>
    simp only [List.filter]
    by_cases hk1 : k ≤ acked1 v
    · rw [decide_eq_true_eq.mpr hk1, decide_eq_true_eq.mpr (Nat.le_trans hk1 (hle v))]
      exact List.Sublist.cons₂ v ih
    · rw [show decide (k ≤ acked1 v) = false from decide_eq_false_iff_not.mpr hk1]
      by_cases hk2 : k ≤ acked2 v
      · rw [decide_eq_true_eq.mpr hk2]; exact List.Sublist.cons v ih
      · rw [show decide (k ≤ acked2 v) = false from decide_eq_false_iff_not.mpr hk2]
        exact ih

/-! ## Proved theorems (CI8 and the four order-statistic theorems) -/

/-- **CI8** — `committedIndex` is 0 when all acked indices are 0. -/
theorem committedIndex_all_zero (voters : List Nat) :
    committedIndex voters (fun _ => 0) = 0 := by
  simp only [committedIndex, sortedAcked]
  apply getD_all_zero
  intro x hx
  have := (sortDesc_perm (voters.map (fun _ => (0 : Nat)))).mem_iff.mp hx
  simp at this; obtain ⟨_, _, rfl⟩ := this; rfl

/-- **CI-Safety** — at least `majority n` voters have acked ≥ `committedIndex`.

    The committed index is `sortedAcked[majority n - 1]`.  Since the sorted list is
    non-increasing, the first `majority n` positions are all ≥ this value, so at
    least `majority n` voters pass the `countGe` threshold. -/
theorem committedIndex_safety (voters : List Nat) (acked : AckedFn)
    (hn : 0 < voters.length) :
    majority voters.length ≤ countGe voters acked (committedIndex voters acked) := by
  have hsa_len : (sortedAcked voters acked).length = voters.length := sortedAcked_length voters acked
  have hmaj_le : majority voters.length ≤ voters.length := by simp [majority]; omega
  have hq_sa : majority voters.length - 1 < (sortedAcked voters acked).length := by
    rw [hsa_len]; simp [majority]; omega
  have hci_eq : committedIndex voters acked =
      (sortedAcked voters acked).get ⟨majority voters.length - 1, hq_sa⟩ :=
    getD_eq_get_of_lt _ _ hq_sa
  rw [countGe_eq_sa_filter, hci_eq]
  apply filter_ge_prefix
  · rw [hsa_len]; exact hmaj_le
  · intro i hi hil
    exact sortDesc_get_antitone (voters.map acked) i (majority voters.length - 1) hi hq_sa
      (by omega)

/-- **CI-Maximality** — `committedIndex` is the largest safe value.

    Any `k > committedIndex` has fewer than `majority n` acked voters: elements
    at positions ≥ `majority n` in the sorted list are all ≤ `committedIndex < k`. -/
theorem committedIndex_maximality (voters : List Nat) (acked : AckedFn)
    (k : Nat) (hk : committedIndex voters acked < k) :
    countGe voters acked k < majority voters.length := by
  by_cases hn : 0 < voters.length
  · have hsa_len : (sortedAcked voters acked).length = voters.length := sortedAcked_length voters acked
    have hq_sa : majority voters.length - 1 < (sortedAcked voters acked).length := by
      rw [hsa_len]; simp [majority]; omega
    have hci_eq : committedIndex voters acked =
        (sortedAcked voters acked).get ⟨majority voters.length - 1, hq_sa⟩ :=
      getD_eq_get_of_lt _ _ hq_sa
    simp only [sortedAcked] at *
    rw [countGe_eq_sa_filter]; simp only [sortedAcked]
    apply Nat.lt_of_le_of_lt
    · apply filter_ge_suffix (q := majority voters.length - 1)
      intro i hi hiq
      have step := sortDesc_get_antitone (voters.map acked) (majority voters.length - 1) i
        hq_sa hi (by omega)
      calc (sortDesc (voters.map acked)).get ⟨i, hi⟩
          ≤ (sortDesc (voters.map acked)).get ⟨majority voters.length - 1, hq_sa⟩ := step
        _ = committedIndex voters acked := hci_eq.symm
        _ < k := hk
    · simp only [majority]; omega
  · cases voters with
    | nil => simp [countGe, majority]
    | cons v vs => simp at hn

/-- **CI-Monotonicity** — committing never regresses when acked indices are non-decreasing.

    Proved via safety and maximality: if `c1 > c2`, safety gives `countGe(acked1, c1) ≥ majority`,
    monotonicity of `countGe` gives `countGe(acked2, c1) ≥ majority`, but maximality of `c2`
    gives `countGe(acked2, c1) < majority` — contradiction. -/
theorem committedIndex_mono (voters : List Nat) (acked1 acked2 : AckedFn)
    (hle : ∀ v, acked1 v ≤ acked2 v) :
    committedIndex voters acked1 ≤ committedIndex voters acked2 := by
  apply Nat.le_of_not_lt; intro hlt
  by_cases hn : 0 < voters.length
  · have h1 := committedIndex_safety voters acked1 hn
    have h2 := countGe_mono_acked voters acked1 acked2 (committedIndex voters acked1) hle
    have h3 := committedIndex_maximality voters acked2 (committedIndex voters acked1) hlt
    omega
  · cases voters with
    | nil => simp [committedIndex, sortedAcked, majority] at hlt
    | cons v vs => simp at hn

end FVSquad.CommittedIndex
