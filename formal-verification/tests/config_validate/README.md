# config_validate Correspondence Tests

> 🔬 *Lean Squad — Task 8 Route B correspondence tests.*

## What is validated

`Config::validate` from `src/config.rs` checks 8 independent constraints on a
`Config` struct. The Lean model `configValidate` in `FVSquad/ConfigValidate.lean`
mirrors each constraint as a boolean conjunction.

## Abstraction

| Lean | Rust |
|------|------|
| `configValidate cfg == true` | `cfg.validate().is_ok()` |
| `configValidate cfg == false` | `cfg.validate().is_err()` |

## Test commands

**Lean (static, at build time):**
```bash
cd formal-verification/lean
lake build FVSquad.ConfigValidateCorrespondence
```

**Rust (runtime):**
```bash
cargo test test_config_validate_correspondence
```

## Reference configuration

```
id=1, heartbeat_tick=2, election_tick=20, min_election_tick=0, max_election_tick=0,
max_inflight_msgs=256, check_quorum=false, read_only_option=Safe,
max_size_per_msg=0, max_uncommitted_size=u64::MAX
```

## Cases (12 total)

| ID | Violated | Expected |
|----|---------|---------|
| 1  | none | true |
| 2  | C1: id=0 | false |
| 3  | C2: heartbeat_tick=0 | false |
| 4  | C3: election_tick=heartbeat_tick | false |
| 5  | C3: election_tick<heartbeat_tick | false |
| 6  | C4: min_election_tick<election_tick | false |
| 7  | none: min=election_tick | true |
| 8  | C5: min=max | false |
| 9  | C6: max_inflight_msgs=0 | false |
| 10 | C7: LeaseBased, check_quorum=false | false |
| 11 | none: LeaseBased, check_quorum=true | true |
| 12 | C8: max_uncommitted < max_size_per_msg | false |

## Result

Both sides agree on all 12 cases. Correspondence level: **Exact**.
