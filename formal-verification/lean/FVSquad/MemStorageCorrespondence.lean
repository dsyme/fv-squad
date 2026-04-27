import FVSquad.MemStorage

/-!
# MemStorageCore Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for the `MemStorageCore`
Lean model against the Rust implementation in `src/storage.rs`.

Each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).  A compile error means the Lean model
gives a different answer than expected.

## Strategy (Task 8, Route B)

Test cases are drawn from the Rust tests in `src/storage.rs`
(`test_storage_first_last_index`, `test_storage_compact`,
`test_storage_append`), and from direct inspection of the `MemStorageCore`
public API.  Both sides must produce the same output on the same input.

- **Lean side**: `#guard` evaluated at lake-build time.
- **Rust side**: `#[test]` in `src/storage.rs` with `assert_eq!`.

## Test cases

### `firstIndex` / `lastIndex`

| ID | snapshotIndex | terms | firstIndex | lastIndex |
|----|---------------|-------|------------|-----------|
| 1  | 4             | [5,5] | 5          | 6         |
| 2  | 0             | []    | 1          | 0         |
| 3  | 9             | [1,2,3] | 10      | 12        |

### `compact`

| ID | before (si, terms) | compactIndex | after (si, terms) |
|----|--------------------|--------------|-------------------|
| 1  | (4, [5,5])         | 5 (= fi; noop) | (4, [5,5])     |
| 2  | (4, [5,5])         | 6            | (5, [5])          |
| 3  | (4, [5,5])         | 3 (< fi; noop) | (4, [5,5])    |

### `append`

| ID | before (si, terms) | startIndex | newTerms | after (si, terms) |
|----|--------------------|------------|----------|-------------------|
| 1  | (4, [5,5])         | 5 (at fi)  | [6,6,6]  | (4, [6,6,6])      |
| 2  | (4, [5,5])         | 6 (extend) | [6]      | (4, [5,6])        |
| 3  | (4, [5,5])         | 7 (append) | [7]      | (4, [5,5,7])      |
| 4  | (4, [5,5,5])       | 5 (replace all from fi) | [6,6] | (4,[6,6]) |
| 5  | (4, [5,5])         | 5          | []       | (4, [5,5]) (noop) |
-/

open FVSquad.MemStorage

namespace FVSquad.MemStorageCorrespondence

/-! ## Helper constructors -/

private def mk (si : Nat) (terms : List Nat) : MemStorageCore :=
  { snapshotIndex := si, terms := terms }

/-! ## `firstIndex` tests -/

-- Case 1: si=4, terms=[5,5] → firstIndex=5
#guard firstIndex (mk 4 [5, 5]) == 5

-- Case 2: si=0, terms=[] → firstIndex=1
#guard firstIndex (mk 0 []) == 1

-- Case 3: si=9, terms=[1,2,3] → firstIndex=10
#guard firstIndex (mk 9 [1, 2, 3]) == 10

/-! ## `lastIndex` tests -/

-- Case 1: si=4, terms=[5,5] → lastIndex=6
#guard lastIndex (mk 4 [5, 5]) == 6

-- Case 2: si=0, terms=[] → lastIndex=0  (empty log: lastIndex < firstIndex)
#guard lastIndex (mk 0 []) == 0

-- Case 3: si=9, terms=[1,2,3] → lastIndex=12
#guard lastIndex (mk 9 [1, 2, 3]) == 12

/-! ## `compact` tests -/

-- Case 1: compactIndex = firstIndex (noop)
#guard compact (mk 4 [5, 5]) 5 == mk 4 [5, 5]

-- Case 2: compactIndex = firstIndex + 1 → drop 1 entry
#guard compact (mk 4 [5, 5]) 6 == mk 5 [5]

-- Case 3: compactIndex < firstIndex (noop)
#guard compact (mk 4 [5, 5]) 3 == mk 4 [5, 5]

-- Case 4: compact entire log (terms becomes [])
#guard compact (mk 4 [5, 5]) 7 == mk 6 []

-- Case 5: compactIndex = 0 (noop, ≤ firstIndex=1 always for si=0)
#guard compact (mk 0 [1, 2]) 0 == mk 0 [1, 2]

/-! ## `append` tests -/

-- Case 1: startIndex = firstIndex; replace all terms
#guard append (mk 4 [5, 5]) 5 [6, 6, 6] == mk 4 [6, 6, 6]

-- Case 2: startIndex = firstIndex + 1; keep 1 entry, append
#guard append (mk 4 [5, 5]) 6 [6] == mk 4 [5, 6]

-- Case 3: startIndex = lastIndex + 1; extend (pure append)
#guard append (mk 4 [5, 5]) 7 [7] == mk 4 [5, 5, 7]

-- Case 4: startIndex = firstIndex, replace all from front
#guard append (mk 4 [5, 5, 5]) 5 [6, 6] == mk 4 [6, 6]

-- Case 5: newTerms empty → noop
#guard append (mk 4 [5, 5]) 5 [] == mk 4 [5, 5]

-- Case 6: startIndex = firstIndex + 2, replace last entry
#guard append (mk 4 [5, 5, 5]) 7 [9, 9] == mk 4 [5, 5, 9, 9]

/-! ## `entryCount` tests -/

#guard entryCount (mk 4 [5, 5]) == 2
#guard entryCount (mk 0 []) == 0
#guard entryCount (compact (mk 4 [5, 5]) 6) == 1

/-! ## Composition -/

-- compact then append restores entries
#guard append (compact (mk 4 [5, 5]) 6) 6 [3, 3] == mk 5 [3, 3]

-- compact is idempotent
#guard compact (compact (mk 4 [5, 5]) 6) 6 == compact (mk 4 [5, 5]) 6

-- double compact (compose): compact to 6 then to 7 = compact straight to 7
#guard compact (compact (mk 4 [5, 5, 5]) 6) 7 == compact (mk 4 [5, 5, 5]) 7

end FVSquad.MemStorageCorrespondence
