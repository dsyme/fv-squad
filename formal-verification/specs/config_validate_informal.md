# Informal Specification: `Config::validate`

**Source**: `src/config.rs`
**Rust function**: `Config::validate(&self) -> Result<()>`

🔬 *Lean Squad — automated formal verification for dsyme/fv-squad.*

---

## Purpose

`Config::validate` checks that a `Config` struct satisfies the invariants required for a Raft node to start correctly. It is a pure, total function (no side effects) that returns `Ok(())` if all constraints pass, or `Err(ConfigInvalid(...))` on the first violated constraint.

It is called exactly once, at node initialisation (`Raft::new`), before any state machine logic runs. A node that passes `validate()` is guaranteed to have self-consistent parameters for elections and heartbeats.

---

## Preconditions

None. `validate` is callable on any `Config` value. It does not panic; all checks are guarded.

The helper methods used internally are:

```
min_election_tick() = if self.min_election_tick == 0 { election_tick } else { self.min_election_tick }
max_election_tick() = if self.max_election_tick == 0 { 2 * election_tick } else { self.max_election_tick }
```

---

## Postconditions

`validate()` returns `Ok(())` **if and only if** all of the following hold simultaneously:

| # | Constraint | Error message key |
|---|-----------|-------------------|
| C1 | `id ≠ 0` (INVALID_ID = 0) | "invalid node id" |
| C2 | `heartbeat_tick ≥ 1` | "heartbeat tick must greater than 0" |
| C3 | `election_tick > heartbeat_tick` | "election tick must be greater than heartbeat tick" |
| C4 | `min_election_tick() ≥ election_tick` | "min election tick must not be less than election_tick" |
| C5 | `min_election_tick() < max_election_tick()` | "min election tick should be less than max election tick" |
| C6 | `max_inflight_msgs ≥ 1` | "max inflight messages must be greater than 0" |
| C7 | `read_only_option = LeaseBased → check_quorum = true` | "read_only_option == LeaseBased requires check_quorum == true" |
| C8 | `max_uncommitted_size ≥ max_size_per_msg` | "max uncommitted size should greater than max_size_per_msg" |

The checks are evaluated in the order C1–C8; the function returns on the **first** failure (short-circuit evaluation). The return value does not communicate which constraint failed beyond the error message string.

---

## Invariants (derived properties)

If `validate()` returns `Ok(())`, the following derived properties hold:

**Election-tick range properties:**

- `election_tick ≥ heartbeat_tick + 1` (from C3)
- `election_tick ≥ 2` (from C2 + C3: `election_tick > heartbeat_tick ≥ 1`)
- `min_election_tick() ≥ election_tick ≥ 2` (from C4 + above)
- `max_election_tick() > min_election_tick() ≥ election_tick` (from C5)
- `max_election_tick() ≥ election_tick + 1` (from C4 + C5)
- When `min_election_tick = 0` (default): `min_election_tick() = election_tick`, constraint C4 trivially holds
- When `max_election_tick = 0` (default): `max_election_tick() = 2 * election_tick`, constraint C5 reduces to `election_tick < 2 * election_tick`, i.e. `election_tick ≥ 1` (satisfied since `election_tick ≥ 2`)

**Default config properties:**
The default `Config` (heartbeat_tick=2, election_tick=20, max_inflight_msgs=256, id=0) fails C1 only (id=0). Setting `id = 1` makes the default config valid.

**Dependency:**
C7 establishes a logical dependency: `LeaseBased ∧ ¬check_quorum → invalid`. Equivalently, the only valid combinations are: `Safe/ReadIndex` (any check_quorum), or `LeaseBased ∧ check_quorum`.

---

## Edge Cases

1. **Zero id**: `id = 0` is always invalid (C1). This prevents the INVALID_ID sentinel being used as a real node id.

2. **Default election tick range**: When both `min_election_tick = 0` and `max_election_tick = 0` (the defaults), the effective range is `[election_tick, 2 * election_tick)`. The constraint C5 then becomes `election_tick < 2 * election_tick`, which holds for any positive `election_tick`.

3. **Custom min/max election tick**: If `min_election_tick` is set explicitly, it must be ≥ `election_tick`. If `max_election_tick` is set explicitly, it must be > `min_election_tick()`. You cannot set `min_election_tick = 10` while `election_tick = 20` (C4 fails: 10 < 20).

4. **max_size_per_msg = 0**: C8 requires `max_uncommitted_size ≥ 0`, which always holds (both are `u64`). So setting `max_size_per_msg = 0` never fails C8.

5. **max_uncommitted_size = NO_LIMIT** (u64::MAX, the default): C8 requires `NO_LIMIT ≥ max_size_per_msg`, which holds since `u64::MAX` is the maximum possible value.

6. **LeaseBased without check_quorum**: Fails C7. This prevents a liveness/safety hazard where a node uses lease-based reads without the quorum-active check that ensures the lease is still valid.

---

## Examples

**Valid config** (all constraints satisfied):
```
id = 1, heartbeat_tick = 2, election_tick = 10,
min_election_tick = 0 (→ 10), max_election_tick = 0 (→ 20),
max_inflight_msgs = 256, check_quorum = false,
read_only_option = Safe, max_uncommitted_size = u64::MAX, max_size_per_msg = 0
→ validate() = Ok(())
```

**Invalid: id = 0**:
```
id = 0 → Err("invalid node id")  (C1 fails)
```

**Invalid: election_tick ≤ heartbeat_tick**:
```
id = 1, heartbeat_tick = 5, election_tick = 5
→ Err("election tick must be greater than heartbeat tick")  (C3 fails)
```

**Invalid: LeaseBased without check_quorum**:
```
id = 1, heartbeat_tick = 1, election_tick = 2, ...,
read_only_option = LeaseBased, check_quorum = false
→ Err("read_only_option == LeaseBased requires check_quorum == true")  (C7 fails)
```

**Invalid: min_election_tick < election_tick**:
```
id = 1, heartbeat_tick = 1, election_tick = 10, min_election_tick = 8, max_election_tick = 20
→ min_election_tick() = 8 < 10 = election_tick → Err("min election tick ... must not be less") (C4 fails)
```

---

## Inferred Intent

The purpose of `validate` is to fail-fast on misconfigured parameters before any Raft state is created. The constraints encode the Raft protocol's timing requirements:
- `election_tick > heartbeat_tick`: a follower must timeout before the leader can heartbeat again
- The election timeout randomisation window `[min, max)` must be non-empty and cover at least `election_tick`
- `max_uncommitted_size ≥ max_size_per_msg`: the proposal queue can always hold at least one message

The ordering of checks (C1 first, C8 last) reflects priority: identity validity is checked before timing, which is checked before capacity.

---

## Open Questions

1. **Q: Why is the `max_uncommitted_size ≥ max_size_per_msg` check (C8) last?** It seems logically independent of the timing checks. Is there a reason it isn't checked first?

2. **Q: Are there additional semantic constraints on `max_apply_unpersisted_log_limit` that should be validated?** The current implementation does not validate this field.

3. **Q: The `id` check only verifies `id ≠ 0`. Is uniqueness of `id` across cluster members enforced anywhere?** (Expected answer: no — uniqueness is a distributed invariant, not checkable locally.)

4. **Q: `max_size_per_msg = 0` is allowed; is this a valid configuration?** The field comment says "0 for at most one entry per message", so it is intentionally valid — but is it actually usable in practice?

---

## Key Propositions for Lean Formalisation

```
-- C1: id validity
theorem validate_id : config.validate = Ok () → config.id ≠ 0

-- C2: heartbeat positive
theorem validate_hb : config.validate = Ok () → config.heartbeat_tick ≥ 1

-- C3: election > heartbeat
theorem validate_election_gt_hb : config.validate = Ok () →
  config.election_tick > config.heartbeat_tick

-- C4: min election tick ≥ election tick
theorem validate_min_election : config.validate = Ok () →
  config.minElectionTick ≥ config.election_tick

-- C5: min < max election tick
theorem validate_tick_range : config.validate = Ok () →
  config.minElectionTick < config.maxElectionTick

-- C6: inflight positive
theorem validate_inflight : config.validate = Ok () → config.max_inflight_msgs ≥ 1

-- C7: lease implies quorum
theorem validate_lease : config.validate = Ok () →
  config.read_only_option = LeaseBased → config.check_quorum = true

-- C8: uncommitted ≥ per_msg
theorem validate_uncommitted : config.validate = Ok () →
  config.max_uncommitted_size ≥ config.max_size_per_msg

-- Completeness: converses also hold (exact characterisation)
theorem validate_ok_iff : config.validate = Ok () ↔ (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ C6 ∧ C7 ∧ C8)

-- Default+id: default config with id ≠ 0 is valid
theorem validate_default_id_pos (h : id ≠ 0) : { Config.default with id }.validate = Ok ()

-- Derived: if valid, election_tick ≥ 2
theorem validate_election_ge_2 : config.validate = Ok () → config.election_tick ≥ 2
```
