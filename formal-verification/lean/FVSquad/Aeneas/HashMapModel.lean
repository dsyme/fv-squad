/-!
# Aeneas Integration: Lean 4 model for Rust's `HashMap<u64, V>` (Step 6 of Epic #46)

Models `std::collections::HashMap<u64, V>` (with `DefaultHashBuilder`) as a
Mathlib `Finmap`.

## Strategy Decision (Step 5 of Epic #46)

### Chosen representation: `Finmap (fun _ : ℕ => V)`

`HashMap<u64, V>` is a finite partial function from `u64` keys to values.  Mathlib's
`Finmap (fun _ : ℕ => V)` is the exact mathematical model, providing:
- `Finmap.lookup`   → `HashMap::get`
- `Finmap.insert`   → `HashMap::insert`
- `Finmap.erase`    → `HashMap::remove`
- `Finmap.keys`     → `HashMap::keys()`

The `u64` keys are modelled as `ℕ` (the same convention used throughout FVSquad).

### Affected modules

| Rust module | HashMap use | Notes |
|-------------|-------------|-------|
| `tracker.rs` | `HashMap<u64, Progress>` (progress map) | Core data structure |
| `tracker.rs` | `HashMap<u64, bool>` (votes) | Used in `vote_result` |
| `read_only.rs` | `HashMap<Vec<u8>, ReadIndexStatus>` | Deferred (see below) |

### `HashMap<Vec<u8>, ReadIndexStatus>` — deferred

`read_only.rs` uses `Vec<u8>` as the key type (a byte-vector request context).
Aeneas would translate this as `List U8`.  Modelling `List U8` equality as a hashable
key requires a `HashMap<List U8, V>` model.  This is deferred to a follow-up because:
1. The existing `FVSquad.ReadOnly` spec already uses an abstract `Context` type.
2. The refinement theorem would parametrize over a `DecidableEq (List U8)` instance.
3. The core Raft safety properties do not depend on the byte content of contexts.

### Recommendation for full pipeline

Once Aeneas produces a Lean translation, replace the `axiom` stubs in the Aeneas
refinement files with the actual `def` bodies.  The `sorry` proofs in this file close
via `simp [Finmap.lookup_insert]` and `omega` (following the same pattern as
`UtilRefinements.lean`).

## Status

🔧 **Skeleton**: All definitions are real (no `axiom`).  Key property theorems carry
`sorry` proofs to be filled in once Aeneas output is available.
-/

import Mathlib.Data.Finmap
import Mathlib.Tactic
import FVSquad.Aeneas.UtilRefinements
import FVSquad.Aeneas.HashSetModel

namespace FVSquad.Aeneas.HashMapModel

open FVSquad.Aeneas.UtilRefinements (AResult AUsize AU64)
open FVSquad.Aeneas.HashSetModel (AHashSet)

/-! ## Core type -/

/-- The Lean model for `HashMap<u64, V>`.

    `AHashMap V` = `Finmap (fun _ : ℕ => V)`.

    Keys are `ℕ` (representing `u64` values); values are generic.
    This is a finite partial function: each key is associated with at most one value. -/
def AHashMap (V : Type) := Finmap (fun _ : ℕ => V)

instance (V : Type) : Inhabited (AHashMap V) := ⟨∅⟩

/-! ## Basic operations -/

/-- Empty map — models `HashMap::new()` and `HashMap::default()`. -/
def AHashMap.mkEmpty (V : Type) : AHashMap V := (∅ : Finmap _)

/-- Insert — models `HashMap::insert(&mut self, key: u64, value: V) -> Option<V>`.

    Returns the updated map (Lean is functional; the old map is not mutated). -/
def AHashMap.insert {V : Type} (m : AHashMap V) (k : AU64) (v : V) : AHashMap V :=
  m.insert k.val v

/-- Lookup — models `HashMap::get(&self, key: &u64) -> Option<&V>`.

    Returns `none` for absent keys, `some v` for present ones. -/
def AHashMap.get {V : Type} (m : AHashMap V) (k : AU64) : Option V :=
  m.lookup k.val

/-- Contains-key — models `HashMap::contains_key(&self, key: &u64) -> bool`. -/
def AHashMap.containsKey {V : Type} (m : AHashMap V) (k : AU64) : Bool :=
  (m.lookup k.val).isSome

/-- Remove — models `HashMap::remove(&mut self, key: &u64) -> Option<V>`. -/
def AHashMap.remove {V : Type} (m : AHashMap V) (k : AU64) : AHashMap V :=
  m.erase k.val

/-- Length — models `HashMap::len(&self) -> usize`. -/
def AHashMap.len {V : Type} (m : AHashMap V) : ℕ := m.keys.card

/-- Key set — models `HashMap::keys()` as the set of present keys. -/
def AHashMap.keySet {V : Type} (m : AHashMap V) : AHashSet := m.keys

/-- Iterate as a list of `(AU64, V)` pairs.

    In Aeneas output, `HashMap` iteration appears as a list (deterministic order is
    not guaranteed in Rust; Aeneas uses an abstract sequence). -/
def AHashMap.toList {V : Type} (m : AHashMap V) : List (AU64 × V) :=
  m.toList.filterMap (fun ⟨k, v⟩ =>
    if h : k < 2 ^ 64 then some (⟨k, h⟩, v) else none)

/-! ## Key properties -/

@[simp] theorem AHashMap.mkEmpty_len (V : Type) :
    (AHashMap.mkEmpty V).len = 0 := by
  simp [AHashMap.mkEmpty, AHashMap.len]

@[simp] theorem AHashMap.insert_get_self {V : Type} (m : AHashMap V) (k : AU64) (v : V) :
    AHashMap.get (AHashMap.insert m k v) k = some v := by
  simp [AHashMap.get, AHashMap.insert, Finmap.lookup_insert]

theorem AHashMap.insert_get_other {V : Type} (m : AHashMap V) (k j : AU64) (v : V)
    (hne : k.val ≠ j.val) :
    AHashMap.get (AHashMap.insert m k v) j = AHashMap.get m j := by
  simp [AHashMap.get, AHashMap.insert, Finmap.lookup_insert_of_ne hne]

@[simp] theorem AHashMap.containsKey_insert {V : Type} (m : AHashMap V) (k : AU64) (v : V) :
    AHashMap.containsKey (AHashMap.insert m k v) k = true := by
  simp [AHashMap.containsKey, AHashMap.get, AHashMap.insert,
        Finmap.lookup_insert]

theorem AHashMap.get_none_iff_not_mem {V : Type} (m : AHashMap V) (k : AU64) :
    AHashMap.get m k = none ↔ k.val ∉ m.keys := by
  simp [AHashMap.get, Finmap.lookup_eq_none]

theorem AHashMap.containsKey_iff_mem {V : Type} (m : AHashMap V) (k : AU64) :
    AHashMap.containsKey m k = true ↔ k.val ∈ m.keys := by
  simp [AHashMap.containsKey, AHashMap.get, Option.isSome_iff_exists,
        Finmap.mem_lookup_iff]

theorem AHashMap.remove_get {V : Type} (m : AHashMap V) (k : AU64) :
    AHashMap.get (AHashMap.remove m k) k = none := by
  simp [AHashMap.get, AHashMap.remove, Finmap.lookup_erase]

/-! ## Specialisations for the modules in Epic #46 -/

/-- **Votes map** — models `HashMap<u64, bool>` in `ProgressTracker::vote_result`.

    In `src/tracker.rs`:
    ```rust
    votes: HashMap<u64, bool>   // Some(true) = granted, Some(false) = rejected
    ```
    The FVSquad model uses a function `u64 → Option Bool`; this bridge gives the
    refined correspondence.
-/
abbrev AVoteMap := AHashMap Bool

/-- Extract the vote result function from the Aeneas vote map.
    Maps absent voters to `none` (not yet heard from), matching `HashMap::get`. -/
def AVoteMap.toVoteFn (m : AVoteMap) : ℕ → Option Bool :=
  fun k => m.lookup k

/-- The Aeneas vote map `m` agrees with a FVSquad check function `chk` when
    `chk v = m.lookup v` for all voters `v`. -/
def AVoteMap.refinesCheckFn (m : AVoteMap) (chk : ℕ → Option Bool) : Prop :=
  ∀ v : ℕ, m.lookup v = chk v

/-! ## Scope: tracker.rs and read_only.rs refinements

The following type aliases declare the Aeneas model types for the remaining HashMap
uses in the codebase.  Full refinement theorems are left as TODOs pending Aeneas output.

### `tracker.rs`: `ProgressMap = HashMap<u64, Progress>`
The value type `Progress` is a struct; the Aeneas-generated Lean type will be named
`Raft.Progress` (or similar).  The FVSquad model already abstracts over an
`AckedIndexer` interface; the bridge is:
```
∀ v ∈ progressMap.keys,
    progressMap.get v = some p → p.matched = ackedFn v
```

### `read_only.rs`: `HashMap<Vec<u8>, ReadIndexStatus>` — deferred
`Vec<u8>` keys cannot be directly modelled as `ℕ`; they would be `List ℕ` (byte lists).
The `ReadOnly` FVSquad spec already uses an abstract `Context` type, so the deferral
is clean.  Once Aeneas gains `Vec<u8>` support, define:
```
abbrev AReadOnlyMap V := AHashMap' (List ℕ) V
```
and add a `DecidableEq (List ℕ)` instance.
-/

end FVSquad.Aeneas.HashMapModel
