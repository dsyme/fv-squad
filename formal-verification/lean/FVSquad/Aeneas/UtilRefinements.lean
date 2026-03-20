/-!
# Aeneas Integration: Lean Refinement Theorems for `src/util.rs`

This file provides the framework for **refinement theorems** that bridge:

- **Aeneas-generated code** — faithful Lean translation of `majority` and `limit_size`
  from `src/util.rs`, produced by running Aeneas with `--features aeneas`
- **FVSquad abstract specifications** — the existing `FVSquad.MajorityQuorum` and
  `FVSquad.LimitSize` modules, already fully proved with 0 sorry

## Status

⬜ **Pending**: Requires running Aeneas on `src/util.rs` to generate the implementation
models.  See `formal-verification/AENEAS_SETUP.md` for setup instructions.

Once Aeneas has been run, replace the `sorry` placeholders below with real proofs.

## Architecture

```
src/util.rs (Rust)
     │
     │  charon + aeneas
     ▼
raft.majority / raft.limitSize  (Aeneas-generated Lean, in this file or adjacent)
     │
     │  refinement theorems (this file)
     ▼
FVSquad.MajorityQuorum.majority / FVSquad.LimitSize.limitSize  (abstract specs)
     │
     │  existing FVSquad proofs
     ▼
Correctness theorems (safety, liveness properties)
```

The refinement theorems give end-to-end Lean-checked confidence that the **actual Rust
code** satisfies the Raft safety properties.

## Usage

Import this file after generating Aeneas output:

```lean
import FVSquad.Aeneas.UtilRefinements
```

-/

import FVSquad.MajorityQuorum
import FVSquad.LimitSize
-- TODO: import Aeneas.Primitives  (from the Aeneas Lean stdlib)
-- TODO: import Raft.Util           (Aeneas-generated from src/util.rs)

namespace FVSquad.Aeneas.UtilRefinements

/-! ## Placeholder: Aeneas-generated definitions

When Aeneas processes `src/util.rs`, it generates Lean definitions similar to these.
Replace this section with the actual generated output.

```lean
-- Expected Aeneas output for majority:
def raft.majority (total : Std.Usize) : Result Std.Usize :=
  -- checked arithmetic: total / 2 + 1
  let half := total / 2#usize
  half + 1#usize

-- Expected Aeneas output for limit_size (sketch — actual signature depends on traits):
def raft.limitSize (entries : alloc.vec.Vec α) (max : Option Std.U64)
    : Result (alloc.vec.Vec α) := ...
```
-/

/-! ## Refinement theorem skeleton: `majority`

Proves that the Aeneas-generated `raft.majority` equals the FVSquad abstract
`MajorityQuorum.majority`, modulo the `Result` monad and `Usize` vs `Nat` types.

Precondition: `n.val / 2 + 1` does not overflow `Usize` (trivially true for any
realistic voter count; usize ≥ 2^32 on all supported platforms).
-/
-- TODO: replace `sorry` with real proof after importing Aeneas output
-- theorem aeneas_majority_refines (n : Std.Usize)
--     (h : n.val / 2 + 1 ≤ Std.Usize.max) :
--     raft.majority n = ok ⟨FVSquad.MajorityQuorum.majority n.val, h⟩ := by
--   simp [raft.majority, FVSquad.MajorityQuorum.majority,
--         Std.Usize.div, Std.Usize.add]
--   omega

/-! ## Refinement theorem skeleton: `limit_size`

Proves that the Aeneas-generated `raft.limitSize` agrees with the FVSquad abstract
`LimitSize.limitSize`, modulo `Result` and the `Vec`/`List` correspondence.

Key correspondence:
- `alloc.vec.Vec α` (Aeneas) ↔ `List Nat` (FVSquad, where `Nat` is byte size)
- `Option Std.U64` (Aeneas) ↔ `Option Nat` (FVSquad)
- `Result (alloc.vec.Vec α)` (Aeneas) ↔ `List Nat` (FVSquad, pure function)
-/
-- TODO: replace `sorry` with real proof after importing Aeneas output and
--       establishing the Vec ↔ List correspondence lemma.
-- theorem aeneas_limitSize_refines (entries : List Nat) (max : Option Nat)
--     (v : alloc.vec.Vec Nat) (hv : v.toList.map Nat.toUSize = entries)
--     (hmax : max.map (·.toNat) = max') :
--     (raft.limitSize v (max.map Std.U64.ofNat)).map alloc.vec.Vec.toList =
--       ok (FVSquad.LimitSize.limitSize entries max') := by
--   sorry

/-! ## Next Steps

1. Run `charon cargo --features aeneas` from the repo root to produce `raft.llbc`
2. Run `aeneas -backend lean -split-files raft.llbc -dest .` to generate Lean files
3. Copy/import the generated `util.lean` (or similar) here
4. Replace the `sorry` stubs above with real proofs
5. Check that the proofs close (0 sorry) using `lake build`

For Lean/Aeneas newcomers: the `progress` tactic in the Aeneas Lean stdlib is
designed specifically for proving properties of Aeneas-generated monadic code.
See the Aeneas examples repository for worked examples.
-/

end FVSquad.Aeneas.UtilRefinements
