import FVSquad.UncommittedState

/-!
# UncommittedState Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `maybe_increase_uncommitted_size`
and `maybe_reduce_uncommitted_size` via `#guard` assertions evaluated at `lake build` time.

## Strategy (Task 8, Route B)

The test cases here mirror `src/raft.rs::test_uncommitted_state_correspondence`.  Both sides
execute the same input/output pairs:

- **Lean side**: `#guard` evaluates the Lean model at compile time.
- **Rust side**: `assert_eq!` in the test verifies at `cargo test` time.

## Modelling summary

The Lean model abstracts over entry byte-size computation:
- `maybeIncrease s size` — `size` is the total byte-size of the proposed entries (pre-computed).
- `maybeReduce s noLimit size` — `noLimit` corresponds to `is_no_limit()`;
  `size` is the pre-filtered byte-size (entries with index > `last_log_tail_index` only).

The Rust `last_log_tail_index` filtering is applied in the test harness before calling the
Lean model, so the `size` argument on both sides represents the same effective byte total.

## Modelling note: noLimit divergence

The Lean `maybeIncrease` model always increments `uncommittedSize` — even in the noLimit
branch. The Rust fast-path returns `true` immediately without updating `uncommitted_size`.

This is a **known modelling simplification**: since `maxUncommittedSize = 0` means "no limit",
the exact value of `uncommittedSize` in that mode does not affect any throttling decision.
Case 1 below tests only the Lean-model semantics; the Rust correspondence test skips the
state assertion for this case (see `check_state: false` in the Rust test).

All other cases (non-noLimit) have full state correspondence between Lean and Rust.

## Case table

### maybeIncrease

| ID | maxUncommitted | uncommitted | size | Expected result    | Expected bool | Scenario |
|----|---------------|-------------|------|--------------------|---------------|---------|
|  1 | 0             | 20          | 10   | uncommitted=30     | true          | noLimit fast path |
|  2 | 100           | 20          | 0    | uncommitted=20     | true          | empty entries |
|  3 | 100           | 0           | 50   | uncommitted=50     | true          | first entry allowed |
|  4 | 100           | 30          | 50   | uncommitted=80     | true          | within budget |
|  5 | 100           | 50          | 51   | uncommitted=50     | false         | over budget |
|  6 | 100           | 50          | 50   | uncommitted=100    | true          | exactly at budget |
|  7 | 100           | 50          | 50+1 | uncommitted=50     | false         | one byte over |
|  8 | 100           | 0           | 200  | uncommitted=200    | true          | first entry (large) |

### maybeReduce

| ID | noLimit | uncommitted | size | Expected result    | Expected bool | Scenario |
|----|---------|-------------|------|--------------------|---------------|---------|
|  9 | true    | 50          | 30   | uncommitted=50     | true          | noLimit fast path |
| 10 | false   | 50          | 0    | uncommitted=50     | true          | empty entries |
| 11 | false   | 50          | 60   | uncommitted=0      | false         | overflow: set to zero |
| 12 | false   | 50          | 30   | uncommitted=20     | true          | normal reduce |
| 13 | false   | 50          | 50   | uncommitted=0      | true          | reduce to exactly zero |

-/

open FVSquad.UncommittedState

/-! ## maybeIncrease correspondence cases -/

-- Case 1: noLimit (max=0) — fast path, always allows
#guard (maybeIncrease { maxUncommittedSize := 0, uncommittedSize := 20 } 10) =
  ({ maxUncommittedSize := 0, uncommittedSize := 30 }, true)

-- Case 2: size=0 — empty entries, always allows
#guard (maybeIncrease { maxUncommittedSize := 100, uncommittedSize := 20 } 0) =
  ({ maxUncommittedSize := 100, uncommittedSize := 20 }, true)

-- Case 3: uncommittedSize=0 — first entry always allowed
#guard (maybeIncrease { maxUncommittedSize := 100, uncommittedSize := 0 } 50) =
  ({ maxUncommittedSize := 100, uncommittedSize := 50 }, true)

-- Case 4: within budget (size + uncommitted ≤ max)
#guard (maybeIncrease { maxUncommittedSize := 100, uncommittedSize := 30 } 50) =
  ({ maxUncommittedSize := 100, uncommittedSize := 80 }, true)

-- Case 5: over budget (size + uncommitted > max) and uncommitted > 0
#guard (maybeIncrease { maxUncommittedSize := 100, uncommittedSize := 50 } 51) =
  ({ maxUncommittedSize := 100, uncommittedSize := 50 }, false)

-- Case 6: exactly at budget (size + uncommitted = max) — allowed
#guard (maybeIncrease { maxUncommittedSize := 100, uncommittedSize := 50 } 50) =
  ({ maxUncommittedSize := 100, uncommittedSize := 100 }, true)

-- Case 7: one byte over budget
#guard (maybeIncrease { maxUncommittedSize := 100, uncommittedSize := 50 } 51) =
  ({ maxUncommittedSize := 100, uncommittedSize := 50 }, false)

-- Case 8: first entry large (uncommitted=0), always allowed regardless of max
#guard (maybeIncrease { maxUncommittedSize := 100, uncommittedSize := 0 } 200) =
  ({ maxUncommittedSize := 100, uncommittedSize := 200 }, true)

/-! ## maybeReduce correspondence cases -/

-- Case 9: noLimit=true fast path — unchanged, returns true
#guard (maybeReduce { maxUncommittedSize := 0, uncommittedSize := 50 } true 30) =
  ({ maxUncommittedSize := 0, uncommittedSize := 50 }, true)

-- Case 10: size=0 — no-op, returns true
#guard (maybeReduce { maxUncommittedSize := 100, uncommittedSize := 50 } false 0) =
  ({ maxUncommittedSize := 100, uncommittedSize := 50 }, true)

-- Case 11: size > uncommitted — overflow, set to zero, returns false
#guard (maybeReduce { maxUncommittedSize := 100, uncommittedSize := 50 } false 60) =
  ({ maxUncommittedSize := 100, uncommittedSize := 0 }, false)

-- Case 12: normal reduce (size ≤ uncommitted)
#guard (maybeReduce { maxUncommittedSize := 100, uncommittedSize := 50 } false 30) =
  ({ maxUncommittedSize := 100, uncommittedSize := 20 }, true)

-- Case 13: reduce to exactly zero (size = uncommitted)
#guard (maybeReduce { maxUncommittedSize := 100, uncommittedSize := 50 } false 50) =
  ({ maxUncommittedSize := 100, uncommittedSize := 0 }, true)
