/-!
# Aeneas Integration: Refinement Theorems for `src/util.rs`

Bridges between:
- **Aeneas-generated code** — faithful Lean 4 translation of `majority` and
  `limit_size` produced by running `aeneas` on `src/util.rs --features aeneas`
- **FVSquad abstract specifications** — `FVSquad.MajorityQuorum` and
  `FVSquad.LimitSize`, already fully proved (0 sorry)

## Architecture

```
src/util.rs (Rust)
     │  charon + aeneas (--features aeneas)
     ▼
Raft.majority / Raft.limitSize   (Aeneas-generated — axiomatised below until run)
     │  refinement theorems (this file)
     ▼
FVSquad.MajorityQuorum.majority / FVSquad.LimitSize.limitSize
     │  existing FVSquad proofs
     ▼
Raft safety properties
```

## Status

🔧 **Skeleton**: The axioms below stand in for the not-yet-generated Aeneas output.
Replace the `axiom` declarations in the `AeneasGenerated` section with the actual
`def` blocks that `aeneas` produces, then the refinement theorems below should close
(replacing `sorry` with real proofs).  See `formal-verification/AENEAS_SETUP.md`.

-/

import Mathlib.Tactic
import FVSquad.MajorityQuorum
import FVSquad.LimitSize

namespace FVSquad.Aeneas.UtilRefinements

/-! ## Aeneas primitive types (minimal mock — replace with real Aeneas stdlib import)

Aeneas generates code over `Primitives.Result`, `Primitives.Usize`, etc.
Until the Aeneas Lean stdlib is imported into this lake project, we axiomatise just
the fragment needed for the refinement statements.
-/

/-- Aeneas `Result`: `ok` for success, `fail` for panics / overflow. -/
inductive AResult (α : Type) where
  | ok   : α → AResult α
  | fail : AResult α
  deriving DecidableEq, Repr

/-- A bounded machine word modelling Aeneas's `Usize`.
    `val` is the mathematical value; `bound` witnesses it fits in `usize`. -/
structure AUsize where
  val   : Nat
  bound : val < 2 ^ 64  -- conservative: usize ≥ 64-bit on all relevant platforms

/-- A bounded 64-bit word modelling Aeneas's `U64`. -/
structure AU64 where
  val   : Nat
  bound : val < 2 ^ 64

/-! ## Section: Aeneas-generated definitions (axiomatised)

Replace these `axiom` declarations with the actual `def` output from Aeneas once the
tool has been run on `src/util.rs` with `--features aeneas`.

```bash
# From the repo root:
charon cargo --features aeneas      # produces raft.llbc
./aeneas/bin/aeneas -backend lean -split-files raft.llbc -dest ./generated
```
-/

/-- Expected Aeneas translation of `pub fn majority(total: usize) -> usize`.

    Rust source (src/util.rs):
    ```rust
    pub fn majority(total: usize) -> usize { total / 2 + 1 }
    ```
    Aeneas wraps arithmetic in `Result` to model potential overflow; in practice
    `total / 2 + 1` never overflows for any realistic voter count. -/
axiom Raft.majority (total : AUsize) : AResult AUsize

/-- Expected Aeneas translation of `pub fn limit_size<T: Message>(entries: &mut Vec<T>,
    max: Option<u64>)`.

    The full signature depends on how Aeneas handles the `Message` trait bound.
    The entries `Vec` is modelled as `List Nat` (byte sizes); `Option AU64` models
    the `max` parameter. -/
axiom Raft.limitSize (entries : List Nat) (max : Option AU64) : AResult (List Nat)

/-! ## Correspondence lemmas

Helper lemmas stating the concrete computation each Aeneas function performs.
These follow directly from the Rust source code and should be provable from the actual
Aeneas output using `simp` + `omega`.
-/

/-- `Raft.majority n` returns `ok (n / 2 + 1)` when the result fits in `usize`.
    This is `sorry`-proved here; it becomes a real proof once the Aeneas output is
    imported and the generated definition is unfolded. -/
theorem Raft.majority_ok (n : AUsize) (h : n.val / 2 + 1 < 2 ^ 64) :
    Raft.majority n = .ok ⟨n.val / 2 + 1, h⟩ := by
  sorry

/-- `Raft.limitSize` with `none` (unlimited) returns the list unchanged. -/
theorem Raft.limitSize_none (entries : List Nat) :
    Raft.limitSize entries none = .ok entries := by
  sorry

/-- `Raft.limitSize` with a finite limit matches the FVSquad model. -/
theorem Raft.limitSize_some (entries : List Nat) (lim : AU64) :
    Raft.limitSize entries (some lim) =
      .ok (FVSquad.LimitSize.limitSize entries (some lim.val)) := by
  sorry

/-! ## Refinement theorems: `majority`

These theorems prove that the Aeneas-generated `Raft.majority` is a faithful
refinement of the FVSquad abstract `MajorityQuorum.majority`.
-/

/-- **majority_refines**: the Aeneas implementation returns the same value as the
    FVSquad abstract majority function, for all `n` that don't overflow `usize`.
    (In practice all voter counts are ≤ a few dozen; overflow is impossible.) -/
theorem majority_refines (n : AUsize) (h : n.val / 2 + 1 < 2 ^ 64) :
    Raft.majority n = .ok ⟨FVSquad.MajorityQuorum.majority n.val, h⟩ := by
  have := Raft.majority_ok n h
  simp [FVSquad.MajorityQuorum.majority] at this ⊢
  exact this

/-- **majority_refines_val**: the result value equals the FVSquad majority. -/
theorem majority_refines_val (n : AUsize) (h : n.val / 2 + 1 < 2 ^ 64)
    (result : AUsize) (hok : Raft.majority n = .ok result) :
    result.val = FVSquad.MajorityQuorum.majority n.val := by
  rw [majority_refines n h] at hok
  cases hok
  rfl

/-! ## Refinement theorems: `limit_size` -/

/-- **limitSize_refines_none**: unlimited case — Aeneas returns the list unchanged,
    agreeing with `FVSquad.LimitSize.limitSize entries none`. -/
theorem limitSize_refines_none (entries : List Nat) :
    Raft.limitSize entries none = .ok (FVSquad.LimitSize.limitSize entries none) := by
  simp [FVSquad.LimitSize.limitSize, Raft.limitSize_none]

/-- **limitSize_refines_some**: limited case — Aeneas result matches the FVSquad
    abstract truncation for any `lim : AU64`. -/
theorem limitSize_refines_some (entries : List Nat) (lim : AU64) :
    Raft.limitSize entries (some lim) =
      .ok (FVSquad.LimitSize.limitSize entries (some lim.val)) :=
  Raft.limitSize_some entries lim

/-- **limitSize_refines**: unified refinement theorem over `Option AU64`. -/
theorem limitSize_refines (entries : List Nat) (max : Option AU64) :
    Raft.limitSize entries max =
      .ok (FVSquad.LimitSize.limitSize entries (max.map (·.val))) := by
  cases max with
  | none     => simp [FVSquad.LimitSize.limitSize, Raft.limitSize_none]
  | some lim => exact Raft.limitSize_some entries lim

/-! ## End-to-end corollary

Composing the refinement theorems with FVSquad's existing safety properties gives
end-to-end guarantees about the actual Rust code.
-/

/-- **majority_at_least_one**: the actual Rust `majority` function always returns ≥ 1,
    because `FVSquad.MajorityQuorum.majority_pos` proves this for the abstract model
    and `majority_refines` bridges to the implementation. -/
theorem majority_at_least_one (n : AUsize) (h : n.val / 2 + 1 < 2 ^ 64)
    (result : AUsize) (hok : Raft.majority n = .ok result) :
    1 ≤ result.val := by
  have hval := majority_refines_val n h result hok
  rw [hval]
  exact FVSquad.MajorityQuorum.majority_pos n.val

/-- **majority_gt_half_impl**: the actual Rust `majority` returns a strict majority.
    Bridges `FVSquad.MajorityQuorum.majority_gt_half` to the implementation. -/
theorem majority_gt_half_impl (n : AUsize) (h : n.val / 2 + 1 < 2 ^ 64)
    (result : AUsize) (hok : Raft.majority n = .ok result) :
    2 * result.val > n.val := by
  have hval := majority_refines_val n h result hok
  rw [hval]
  exact FVSquad.MajorityQuorum.majority_gt_half n.val

end FVSquad.Aeneas.UtilRefinements
