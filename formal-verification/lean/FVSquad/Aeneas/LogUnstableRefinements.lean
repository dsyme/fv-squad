/-!
# Aeneas Integration: Refinement Theorems for `src/log_unstable.rs`  (Step 4)

Bridges between:
- **Aeneas-generated code** — Lean 4 translation of key operations from
  `src/log_unstable.rs` (which is fully within Aeneas's safe subset; no unsafe code)
- **FVSquad abstract specification** — `FVSquad.UnstableLog`, already proved with
  well-formedness preservation and operation theorems

## Aeneas feasibility of `log_unstable.rs`

`log_unstable.rs` is immediately Aeneas-compatible:
- No `unsafe` blocks (no feature guard needed — unlike `committed_index`)
- Uses only `Vec`, `Option`, primitive integers — all in Aeneas's stdlib
- The `slog::Logger` field is a side-effect-only dependency; Aeneas ignores `Logger`
  fields when they don't affect the return value

The only stub needed is for `slog::Logger` (as an opaque unit type).

## Key functions to refine

| Rust function | FVSquad model | Notes |
|---------------|---------------|-------|
| `maybe_first_index` | `maybeFirstIndex` | Pure; easy |
| `maybe_last_index` | `maybeLastIndex` | Pure; easy |
| `maybe_term` | `maybeTerm` | Pure; easy |
| `stable_entries` | `stableEntries` | Mutates in place; model as pure |
| `stable_snap` | `stableSnap` | Mutates in place; model as pure |
| `restore` | `restore` | Pure (ignores logger) |
| `truncate_and_append` | `truncateAndAppend` | Core operation |

## Status

🔧 **Skeleton**: The axioms stand in for not-yet-generated Aeneas output.
`log_unstable.rs` requires **no Cargo feature guard** — it is already in Aeneas's
safe subset.  Run `charon cargo` (without `--features aeneas`) to extract it.

See `formal-verification/AENEAS_SETUP.md` for setup instructions.

-/

import Mathlib.Tactic
import FVSquad.UnstableLog
import FVSquad.Aeneas.UtilRefinements  -- for AResult, AUsize, AU64

namespace FVSquad.Aeneas.LogUnstableRefinements

open FVSquad.UnstableLog
open FVSquad.Aeneas.UtilRefinements (AResult AUsize AU64)

/-! ## Aeneas types for `log_unstable.rs` -/

/-- Aeneas model of a Raft log entry.  Aeneas generates a struct matching the
    protobuf-generated `Entry`; we model just index and term (the fields used in
    FVSquad).  The `data` and `context` blobs are abstracted as `Bool` placeholders
    (their content is irrelevant to the index/term arithmetic). -/
structure AEntry where
  index : AU64
  term  : AU64
  deriving Repr

/-- Aeneas model of `SnapshotMetadata`. -/
structure ASnapMeta where
  index : AU64
  term  : AU64
  deriving Repr

/-- Aeneas model of the `Unstable` struct.  `logger` is dropped (Aeneas ignores it
    for arithmetic operations). -/
structure AUnstable where
  offset   : AU64
  entries  : List AEntry
  snapshot : Option ASnapMeta
  deriving Repr

/-! ## Correspondence functions: Aeneas ↔ FVSquad -/

/-- Convert an `AEntry` to the FVSquad `Entry`. -/
def toEntry (e : AEntry) : Entry := { index := e.index.val, term := e.term.val }

/-- Convert a `ASnapMeta` to the FVSquad `SnapMeta`. -/
def toSnapMeta (s : ASnapMeta) : SnapMeta := { index := s.index.val, term := s.term.val }

/-- Convert an `AUnstable` to the FVSquad `Unstable`. -/
def toUnstable (u : AUnstable) : Unstable :=
  { offset   := u.offset.val
  , entries  := u.entries.map toEntry
  , snapshot := u.snapshot.map toSnapMeta }

/-! ## Section: Aeneas-generated definitions (axiomatised)

Replace these `axiom` declarations with the actual Aeneas output once run on
`src/log_unstable.rs`.  Unlike `majority.rs`, no `--features aeneas` flag is needed.

```bash
# From the repo root — no extra features needed:
charon cargo                      # produces raft.llbc
./aeneas/bin/aeneas -backend lean -split-files raft.llbc -dest ./generated
# The generated file for log_unstable.rs will contain the definitions below.
```
-/

/-- Aeneas translation of `maybe_first_index`. -/
axiom Raft.Unstable.maybeFirstIndex (u : AUnstable) : Option AU64

/-- Aeneas translation of `maybe_last_index`. -/
axiom Raft.Unstable.maybeLastIndex (u : AUnstable) : Option AU64

/-- Aeneas translation of `maybe_term`. -/
axiom Raft.Unstable.maybeTerm (u : AUnstable) (idx : AU64) : AResult (Option AU64)

/-- Aeneas translation of `stable_entries` (side-effect-free model). -/
axiom Raft.Unstable.stableEntries (u : AUnstable) : AResult AUnstable

/-- Aeneas translation of `stable_snap` (side-effect-free model). -/
axiom Raft.Unstable.stableSnap (u : AUnstable) : AResult AUnstable

/-- Aeneas translation of `restore`. -/
axiom Raft.Unstable.restore (u : AUnstable) (snap : ASnapMeta) : AResult AUnstable

/-- Aeneas translation of `truncate_and_append`. -/
axiom Raft.Unstable.truncateAndAppend (u : AUnstable) (ents : List AEntry) : AResult AUnstable

/-! ## Correspondence axioms

These state what each Aeneas function computes, expressed in terms of the FVSquad
model.  They are `sorry`-proved until the Aeneas `def` bodies are imported.
-/

theorem Raft.Unstable.maybeFirstIndex_spec (u : AUnstable) :
    (Raft.Unstable.maybeFirstIndex u).map (·.val) =
      FVSquad.UnstableLog.maybeFirstIndex (toUnstable u) := by
  sorry

theorem Raft.Unstable.maybeLastIndex_spec (u : AUnstable) :
    (Raft.Unstable.maybeLastIndex u).map (·.val) =
      FVSquad.UnstableLog.maybeLastIndex (toUnstable u) := by
  sorry

theorem Raft.Unstable.maybeTerm_spec (u : AUnstable) (idx : AU64) :
    (Raft.Unstable.maybeTerm u idx).map (Option.map (·.val)) =
      .ok (FVSquad.UnstableLog.maybeTerm (toUnstable u) idx.val) := by
  sorry

theorem Raft.Unstable.stableEntries_spec (u : AUnstable) :
    (Raft.Unstable.stableEntries u).map toUnstable =
      .ok (FVSquad.UnstableLog.stableEntries (toUnstable u)) := by
  sorry

theorem Raft.Unstable.stableSnap_spec (u : AUnstable) :
    (Raft.Unstable.stableSnap u).map toUnstable =
      .ok (FVSquad.UnstableLog.stableSnap (toUnstable u)) := by
  sorry

theorem Raft.Unstable.restore_spec (u : AUnstable) (snap : ASnapMeta) :
    (Raft.Unstable.restore u snap).map toUnstable =
      .ok (FVSquad.UnstableLog.restore (toUnstable u) (toSnapMeta snap)) := by
  sorry

theorem Raft.Unstable.truncateAndAppend_spec (u : AUnstable) (ents : List AEntry) :
    (Raft.Unstable.truncateAndAppend u ents).map toUnstable =
      .ok (FVSquad.UnstableLog.truncateAndAppend (toUnstable u) (ents.map toEntry)) := by
  sorry

/-! ## Refinement theorems -/

/-- **maybeFirstIndex_refines**: the Aeneas implementation returns the same first index
    as the FVSquad abstract model. -/
theorem maybeFirstIndex_refines (u : AUnstable) :
    (Raft.Unstable.maybeFirstIndex u).map (·.val) =
      (toUnstable u).snapshot.map (fun s => s.index + 1) := by
  rw [Raft.Unstable.maybeFirstIndex_spec]
  simp [FVSquad.UnstableLog.maybeFirstIndex, toUnstable, toSnapMeta]

/-- **maybeLastIndex_refines**: the Aeneas implementation returns the same last index. -/
theorem maybeLastIndex_refines (u : AUnstable) :
    (Raft.Unstable.maybeLastIndex u).map (·.val) =
      FVSquad.UnstableLog.maybeLastIndex (toUnstable u) :=
  Raft.Unstable.maybeLastIndex_spec u

/-- **wellFormed_preserved_by_restore**: `restore` preserves the well-formedness invariant.
    This is the key safety property: the `Unstable` buffer cannot become incoherent. -/
theorem wellFormed_preserved_by_restore
    (u : AUnstable) (snap : ASnapMeta)
    (hw : wellFormed (toUnstable u))
    (result : AUnstable)
    (hok : Raft.Unstable.restore u snap = .ok result) :
    wellFormed (toUnstable result) := by
  have hspec := Raft.Unstable.restore_spec u snap
  rw [hok] at hspec
  simp at hspec
  rw [← hspec]
  exact FVSquad.UnstableLog.restore_wellFormed (toUnstable u) (toSnapMeta snap) hw

/-- **wellFormed_preserved_by_stableEntries**: clearing stable entries preserves
    well-formedness. -/
theorem wellFormed_preserved_by_stableEntries
    (u : AUnstable)
    (hw : wellFormed (toUnstable u))
    (result : AUnstable)
    (hok : Raft.Unstable.stableEntries u = .ok result) :
    wellFormed (toUnstable result) := by
  have hspec := Raft.Unstable.stableEntries_spec u
  rw [hok] at hspec
  simp at hspec
  rw [← hspec]
  constructor
  · exact FVSquad.UnstableLog.stableEntries_indexCoherent (toUnstable u)
  · simp [FVSquad.UnstableLog.wellFormed, FVSquad.UnstableLog.stableEntries,
          FVSquad.UnstableLog.snapCoherent]

/-! ## Next steps

1. Run `charon cargo` (no feature flag needed for `log_unstable.rs`)
2. Run `aeneas -backend lean -split-files raft.llbc -dest ./generated`
3. Import the generated `log_unstable.lean` and replace the `axiom` declarations
   with `open` or `alias` directives pointing to the generated definitions
4. Replace `sorry` proofs with real proofs using `simp` + `omega` + `progress`
5. Extend to cover `truncateAndAppend` well-formedness (the most complex case)

The `progress` tactic from the Aeneas Lean stdlib is designed for step 4.
-/

end FVSquad.Aeneas.LogUnstableRefinements
