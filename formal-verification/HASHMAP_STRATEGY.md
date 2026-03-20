# Aeneas Step 5: HashMap/HashSet Scope Evaluation

*This document records the evaluation for Step 5 of Epic #46: evaluate the scope
and decide on a strategy for HashMap/HashSet in the Aeneas integration pipeline.*

## Summary

| Type | Lean model | Lean file | Status |
|------|------------|-----------|--------|
| `HashSet<u64>` | `Finset ℕ` | `FVSquad/Aeneas/HashSetModel.lean` | ✅ Complete |
| `HashMap<u64, V>` | `Finmap (fun _ : ℕ => V)` | `FVSquad/Aeneas/HashMapModel.lean` | ✅ Complete |
| `HashMap<Vec<u8>, V>` | Deferred | — | ⏸ Deferred |

## Affected modules

### Immediately unblocked (with HashSet/HashMap models)

| Rust file | Type | Fields / uses | FVSquad spec |
|-----------|------|---------------|--------------|
| `src/quorum/majority.rs` | `HashSet<u64>` | `Configuration.voters` | `CommittedIndex.lean` |
| `src/tracker.rs` | `HashSet<u64>` | `learners`, `learners_next` | `QuorumRecentlyActive.lean` |
| `src/tracker.rs` | `HashMap<u64, Progress>` | `progress` (ProgressMap) | `ProgressTracking.lean` |
| `src/tracker.rs` | `HashMap<u64, bool>` | `votes` | `MajorityQuorum.lean` |
| `src/quorum/joint.rs` | `HashSet<u64>` | inner `Configuration.voters` | `JointQuorum.lean` |

All five uses involve `u64` keys, which map directly to `ℕ` in the Lean model.

### Deferred: `HashMap<Vec<u8>, ReadIndexStatus>` in `read_only.rs`

`Vec<u8>` keys require modelling Rust's byte-vector equality as a Lean key type.

- The FVSquad `ReadOnly.lean` spec already uses an abstract `Context` type, so the
  existing proofs are unaffected.
- A future step can define `AHashMapByteKey V := Finmap (fun _ : List ℕ => V)` with
  a `DecidableEq (List ℕ)` instance (which Lean provides automatically).
- This deferral does not block any current proof obligations.

## Strategy: why `Finset ℕ` for `HashSet<u64>`

1. **Exact model**: `HashSet<u64>` is a finite set of distinct `u64` integers.
   `Finset ℕ` is exactly this (with `u64 ↔ ℕ` via `.val`).

2. **Already used**: every existing FVSquad voter set is a `Finset ℕ`.  No bridge
   conversion is needed at the spec–refinement boundary.

3. **Massive theorem library**: Mathlib's `Finset` API covers all operations needed.

4. **Aeneas serialisation**: when Aeneas cannot translate a `HashSet` directly, it
   passes the set as an iteration list (`List AU64`).  The `ofList` function in
   `HashSetModel.lean` converts this back to `Finset ℕ`.

## Strategy: why `Finmap` for `HashMap<u64, V>`

1. **Exact model**: `HashMap<u64, V>` is a finite partial function `u64 → Option V`.
   Mathlib's `Finmap` is exactly this.

2. **Clean API**: `Finmap.lookup`, `Finmap.insert`, `Finmap.erase` mirror
   `HashMap::get`, `HashMap::insert`, `HashMap::remove`.

3. **Bridge to FVSquad**: the `AVoteMap.toVoteFn` function in `HashMapModel.lean`
   converts an Aeneas vote map to the `(u64 → Option bool)` function expected by
   `MajorityQuorum.voteResult`.

## Impact on Aeneas integration plan

With Steps 5 and 6 complete, the Aeneas pipeline can now be extended to cover:

- **`src/quorum/majority.rs`**: `committed_index` refinement (skeleton already in
  `CommittedIndexRefinements.lean`; can now use `AHashSet` properly)
- **`src/tracker.rs`**: new `TrackerRefinements.lean` skeleton
- **`src/quorum/joint.rs`**: new `JointQuorumRefinements.lean` skeleton

The remaining blocker for a full end-to-end proof is running `charon` + `aeneas`
on the repo (see `AENEAS_SETUP.md`) and replacing the `axiom` stubs with generated
`def` bodies.
