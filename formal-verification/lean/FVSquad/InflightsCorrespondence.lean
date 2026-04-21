import FVSquad.Inflights

/-!
# Inflights Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `Inflights` operations:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/inflights/cases.json` are
mirrored both here (Lean model side) and in
`src/tracker/inflights.rs::test_inflights_correspondence`
(Rust source side).  Both sides must produce the same outcome on the same
sequence of operations.

- **Lean side**: `#guard` evaluates expressions over `Inflights.add / freeTo / ...`
  at lake-build time.
- **Rust side**: corresponding `Inflights` operations verified at `cargo test` time.

## Abstraction

The Lean model uses a simple `{ queue : List Nat, cap : Nat }` (purely functional).
The Rust implementation uses a ring buffer.  The `logicalContent` function in
`Inflights.lean` bridges the two representations: the abstract model's `queue` equals
the ring buffer's logical content in order.

## Test cases (12 total)

| ID | Operations | Observable | Expected | Notes |
|----|-----------|-----------|---------|-------|
| 1  | new(3) | count | 0 | fresh buffer empty |
| 2  | new(3) | full | false | 0 < 3 |
| 3  | new(3).add(10) | queue | [10] | single add |
| 4  | new(3).add(10).add(20) | count | 2 | two adds |
| 5  | new(3).add(10).add(20).add(30) | full | true | 3 = cap |
| 6  | new(3).add(10).add(20).freeTo(10) | queue | [20] | free first entry |
| 7  | new(3).add(10).add(20).add(30).freeTo(20) | queue | [30] | free first two |
| 8  | new(3).add(10).add(20).freeTo(25) | queue | [] | free all ≤ 25 |
| 9  | new(3).add(10).add(20).freeFirstOne | queue | [20] | free first one |
| 10 | new(3).add(10).add(20).reset | queue | [] | reset clears all |
| 11 | new(3).add(10).reset | full | false | after reset not full |
| 12 | new(1).add(10) | full | true | cap=1, one entry |
-/

namespace FVSquad.InflightsCorrespondence

open FVSquad.Inflights

/-- Construct an empty Inflights with given capacity. -/
private def newInf (cap : Nat) : Inflights := { queue := [], cap := cap }

/-! ## Case 1: fresh buffer is empty (count = 0) -/

#guard (newInf 3).count == 0

/-! ## Case 2: fresh buffer is not full -/

#guard (newInf 3).full == false

/-! ## Case 3: single add produces queue [10] -/

#guard ((newInf 3).add 10).queue == [10]

/-! ## Case 4: two adds → count = 2 -/

#guard ((newInf 3).add 10 |>.add 20).count == 2

/-! ## Case 5: three adds on cap-3 buffer → full -/

#guard (((newInf 3).add 10).add 20 |>.add 30).full == true

/-! ## Case 6: add 10, add 20, freeTo 10 → queue = [20] -/

#guard (((newInf 3).add 10).add 20 |>.freeTo 10).queue == [20]

/-! ## Case 7: add 10,20,30, freeTo 20 → queue = [30] -/

#guard ((((newInf 3).add 10).add 20).add 30 |>.freeTo 20).queue == [30]

/-! ## Case 8: add 10, add 20, freeTo 25 → queue = [] (all freed) -/

#guard (((newInf 3).add 10).add 20 |>.freeTo 25).queue == []

/-! ## Case 9: add 10, add 20, freeFirstOne → queue = [20] -/

#guard (((newInf 3).add 10).add 20 |>.freeFirstOne).queue == [20]

/-! ## Case 10: add 10, add 20, reset → queue = [] -/

#guard (((newInf 3).add 10).add 20 |>.reset).queue == []

/-! ## Case 11: add then reset → not full -/

#guard ((newInf 3).add 10 |>.reset).full == false

/-! ## Case 12: cap=1, one add → full -/

#guard ((newInf 1).add 10).full == true

end FVSquad.InflightsCorrespondence
