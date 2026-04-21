import FVSquad.LimitSize

/-!
# LimitSize Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `limit_size`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/limit_size/cases.json` are
mirrored both here (Lean model side) and in
`src/util.rs::test_limit_size_correspondence`
(Rust source side).  Both sides must produce the same list length on the same
`(sizes, budget)` input.

- **Lean side**: `#guard` evaluates `(limitSize id sizes (some budget)).length == expected`
  at lake-build time.
- **Rust side**: `assert_eq!` in the test verifies the same truncation at `cargo test` time.

## Abstraction

The Lean model uses `id : Nat → Nat` as the size function (each entry's value IS its size).
On the Rust side, entries are `Entry` objects whose `compute_size()` equals the
corresponding natural number.  For a prost `Entry` with only `data` set to `n` bytes:
  `encoded_len() = 2 + n` (1-byte tag for field 4, 1-byte varint, n data bytes).
So a Lean entry of value `100` corresponds to a Rust `Entry { data: vec![0u8; 98] }`.

## Test cases (10 total)

| ID | sizes | budget | expected_len | Notes |
|----|-------|--------|-------------|-------|
| 1  | [] | any | 0 | empty list unchanged |
| 2  | [100] | 0 | 1 | singleton unchanged regardless of budget |
| 3  | [100,100,100,100,100] | none (no test) | — | no-limit: all kept |
| 4  | [100,100,100,100,100] | 500 | 5 | all fit: 500 ≤ 500 |
| 5  | [100,100,100,100,100] | 400 | 4 | 4th kept (400≤400), 5th makes 500>400 |
| 6  | [100,100,100,100,100] | 220 | 2 | 2nd kept (200≤220), 3rd makes 300>220 |
| 7  | [100,100,100,100,100] | 100 | 1 | first always kept, 2nd makes 200>100 |
| 8  | [100,100,100,100,100] | 0 | 1 | budget 0: first always kept |
| 9  | [200,100,100] | 350 | 2 | first (200), second: 300≤350 → keep; third: 400>350 → stop |
| 10 | [200,100,100] | 200 | 1 | first (200), second: 300>200 → stop |
-/

namespace FVSquad.LimitSizeCorrespondence

/-! ## Case 1: Empty list → unchanged (length = 0) -/

#guard (limitSize id [] (some 100)).length == 0

/-! ## Case 2: Singleton → unchanged even with budget 0 -/

#guard (limitSize id [100] (some 0)).length == 1

/-! ## Case 3: 5 entries, budget 500 → all kept (5th cumulative = 500 ≤ 500) -/

#guard (limitSize id [100, 100, 100, 100, 100] (some 500)).length == 5

/-! ## Case 4: 5 entries, budget 400 → 4 kept
    Trace: first kept (k=0→always), then cum=100; 200≤400→k=2, cum=200; 300≤400→k=3,
    cum=300; 400≤400→k=4, cum=400; 500>400→stop. Take 4. -/

#guard (limitSize id [100, 100, 100, 100, 100] (some 400)).length == 4

/-! ## Case 5: 5 entries, budget 220 → 2 kept
    First: k=0→always, cum=100. Second: 200≤220→k=2, cum=200. Third: 300>220→stop. -/

#guard (limitSize id [100, 100, 100, 100, 100] (some 220)).length == 2

/-! ## Case 6: 5 entries, budget 100 → 1 kept (first always; second: 200>100 → stop) -/

#guard (limitSize id [100, 100, 100, 100, 100] (some 100)).length == 1

/-! ## Case 7: 5 entries, budget 0 → 1 kept (first always; second: 100>0 → stop) -/

#guard (limitSize id [100, 100, 100, 100, 100] (some 0)).length == 1

/-! ## Case 8: Mixed sizes [200,100,100], budget 350 → 2 kept
    First: always (k=0), cum=200. Second: 300≤350→k=2, cum=300. Third: 400>350→stop. -/

#guard (limitSize id [200, 100, 100] (some 350)).length == 2

/-! ## Case 9: Mixed sizes [200,100,100], budget 200 → 1 kept
    First: always, cum=200. Second: 300>200 → stop. -/

#guard (limitSize id [200, 100, 100] (some 200)).length == 1

/-! ## Case 10: no-limit case → all kept -/

#guard (limitSize id [100, 100, 100] none).length == 3

end FVSquad.LimitSizeCorrespondence
