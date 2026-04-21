import FVSquad.ConfigValidate

/-!
# ConfigValidate Correspondence Tests — Lean 4

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides **static correspondence validation** for `config_validate`:
each `#guard` assertion runs the Lean model on a concrete test case and verifies
the result at compile time (`lake build`).

## Strategy (Task 8, Route B)

The test cases in `formal-verification/tests/config_validate/cases.json` are
mirrored both here (Lean model side) and in
`src/config.rs::test_config_validate_correspondence`
(Rust source side).  Both sides must produce the same `expected` Bool on the same
Config input.

- **Lean side**: `#guard` evaluates `configValidate cfg == expected` at lake-build time.
- **Rust side**: `assert_eq!(cfg.validate().is_ok(), expected)` at `cargo test` time.

## What is checked

For each case we verify one observable property:
  `configValidate cfg == expected`

where `expected` is `true` iff `Config::validate()` returns `Ok(())`.

## Default configuration

The reference config (matches `Config::default()` with `id=1`):
```
id=1, heartbeat_tick=2, election_tick=20, min_election_tick=0, max_election_tick=0,
max_inflight_msgs=256, check_quorum=false, read_only_option=Safe,
max_size_per_msg=0, max_uncommitted_size=18446744073709551615
```

## Test cases (12 total)

| ID | Description | Violated | Expected |
|----|-------------|---------|---------|
| 1  | default config | none | true |
| 2  | id = 0 | C1: validId | false |
| 3  | heartbeat_tick = 0 | C2: validHeartbeat | false |
| 4  | election_tick = heartbeat_tick | C3: validElection | false |
| 5  | election_tick < heartbeat_tick | C3: validElection | false |
| 6  | min_election_tick < election_tick | C4: validMinTick | false |
| 7  | min_election_tick = election_tick (valid) | none | true |
| 8  | min_election_tick = max_election_tick | C5: validTickRange | false |
| 9  | max_inflight_msgs = 0 | C6: validInflight | false |
| 10 | LeaseBased without check_quorum | C7: validReadOnly | false |
| 11 | LeaseBased with check_quorum | none | true |
| 12 | max_uncommitted_size < max_size_per_msg | C8: validUncommitted | false |
-/

namespace FVSquad.ConfigValidateCorrespondence

/-- Reference default configuration (matches Config::default() with id=1). -/
private def base : Config :=
  { id := 1, heartbeat_tick := 2, election_tick := 20,
    min_election_tick := 0, max_election_tick := 0,
    max_inflight_msgs := 256, check_quorum := false,
    read_only_option := ReadOnlyOption.Safe,
    max_size_per_msg := 0, max_uncommitted_size := UInt64.size }

/-! ## Case 1: default config → valid -/

#guard configValidate base == true

/-! ## Case 2: id = 0 → invalid (C1: validId violated) -/

#guard configValidate { base with id := 0 } == false

/-! ## Case 3: heartbeat_tick = 0 → invalid (C2: validHeartbeat violated) -/

#guard configValidate { base with heartbeat_tick := 0 } == false

/-! ## Case 4: election_tick = heartbeat_tick → invalid (C3: must be strictly greater) -/

#guard configValidate { base with election_tick := 2 } == false

/-! ## Case 5: election_tick < heartbeat_tick → invalid (C3) -/

#guard configValidate { base with election_tick := 1 } == false

/-! ## Case 6: min_election_tick < election_tick → invalid (C4: minTick < election_tick)
    minTick = min_election_tick = 10 < election_tick = 20 → invalid -/

#guard configValidate { base with min_election_tick := 10 } == false

/-! ## Case 7: min_election_tick = election_tick → valid
    minTick = 20 = election_tick; maxTick = 40 (0 → 2*20); 20 < 40 → valid -/

#guard configValidate { base with min_election_tick := 20 } == true

/-! ## Case 8: min = max election tick → invalid (C5: minTick < maxTick violated)
    min=20 set explicitly; max=20 set explicitly; 20 < 20 is false → invalid -/

#guard configValidate { base with min_election_tick := 20, max_election_tick := 20 } == false

/-! ## Case 9: max_inflight_msgs = 0 → invalid (C6: validInflight violated) -/

#guard configValidate { base with max_inflight_msgs := 0 } == false

/-! ## Case 10: LeaseBased without check_quorum → invalid (C7: validReadOnly violated) -/

#guard configValidate { base with read_only_option := ReadOnlyOption.LeaseBased } == false

/-! ## Case 11: LeaseBased with check_quorum = true → valid -/

#guard configValidate { base with read_only_option := ReadOnlyOption.LeaseBased, check_quorum := true } == true

/-! ## Case 12: max_uncommitted_size < max_size_per_msg → invalid (C8: validUncommitted violated) -/

#guard configValidate { base with max_size_per_msg := 100, max_uncommitted_size := 50 } == false

end FVSquad.ConfigValidateCorrespondence
