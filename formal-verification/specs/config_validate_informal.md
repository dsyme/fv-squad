# Informal Specification: `Config::validate`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

**Source**: `src/config.rs` — `impl Config { fn validate(&self) -> Result<()> }`

---

## Purpose

`Config::validate` checks that a Raft configuration is well-formed before starting a node.
It is a pure predicate over scalar fields of `Config`; it does not mutate any state.
Returns `Ok(())` if all constraints are satisfied, or `Err(ConfigInvalid(_))` on the first violated constraint.

---

## Configuration fields relevant to validation

| Field | Type | Default | Meaning |
|-------|------|---------|---------|
| `id` | `u64` | `0` | Node identity. Must be non-zero. |
| `heartbeat_tick` | `usize` | `2` | Leader heartbeat interval in ticks. |
| `election_tick` | `usize` | `20` | Follower election timeout in ticks. |
| `min_election_tick` | `usize` | `0` (= `election_tick`) | Lower bound of randomised election timeout. |
| `max_election_tick` | `usize` | `0` (= `2 * election_tick`) | Upper bound (exclusive) of randomised election timeout. |
| `max_inflight_msgs` | `usize` | `256` | Max in-flight append messages. |
| `check_quorum` | `bool` | `false` | Whether leader checks quorum activity. |
| `read_only_option` | `ReadOnlyOption` | `Safe` | Linearizability mode; `LeaseBased` requires `check_quorum`. |
| `max_uncommitted_size` | `u64` | `NO_LIMIT` | Max bytes of uncommitted entries; must be ≥ `max_size_per_msg`. |
| `max_size_per_msg` | `u64` | `0` | Max bytes per append message. |

Note: `min_election_tick` and `max_election_tick` are *canonicalised* before checking:
- `min_timeout = if min_election_tick == 0 { election_tick } else { min_election_tick }`
- `max_timeout = if max_election_tick == 0 { 2 * election_tick } else { max_election_tick }`

---

## Preconditions

None. The function is total: it can be called on any `Config` value.

---

## Postconditions

`validate` returns `Ok(())` **if and only if** all of the following hold:

1. **Valid node ID**: `id ≠ 0`
2. **Positive heartbeat**: `heartbeat_tick > 0`
3. **Election timeout dominates heartbeat**: `election_tick > heartbeat_tick`
4. **Min election tick is at least election tick**: `min_timeout ≥ election_tick`
   - Equivalently: `min_election_tick == 0 ∨ min_election_tick ≥ election_tick`
5. **Timeout range is non-trivial**: `min_timeout < max_timeout`
   - Equivalently: the randomised election timeout range is non-empty
6. **Positive inflight limit**: `max_inflight_msgs > 0`
7. **Lease-based reads require quorum check**: `read_only_option == LeaseBased → check_quorum`
8. **Uncommitted size respects message size**: `max_uncommitted_size ≥ max_size_per_msg`

The check is short-circuit: constraints are evaluated in order 1–8 and the first
failure is returned. The *set* of valid configs is independent of order, but error
reporting is order-dependent.

---

## Invariants

The set of valid configs satisfies a conjunction of independent constraints.
There is no global invariant connecting them beyond the individual predicates.

---

## Edge cases

- **Default config with `id = 0`**: fails constraint 1 immediately.
  `Config::new(0)` is invalid; `Config::new(1)` with all defaults is valid.
- **`min_election_tick = election_tick - 1`**: fails constraint 4 (one less than election_tick).
- **`min_election_tick = max_election_tick`**: fails constraint 5 (empty range).
- **`read_only_option = LeaseBased, check_quorum = false`**: fails constraint 7.
- **`max_uncommitted_size < max_size_per_msg`**: fails constraint 8.
- **`heartbeat_tick = 0`**: fails constraint 2 before constraint 3 is reached.

---

## Examples

| id | hb | el | min_el | max_el | inflight | read_only | check_q | max_uncommit | max_msg | Result |
|----|----|----|--------|--------|----------|-----------|---------|--------------|---------|--------|
| 1  | 2  | 20 | 0      | 0      | 256      | Safe      | false   | NO_LIMIT     | 0       | Ok     |
| 0  | 2  | 20 | 0      | 0      | 256      | Safe      | false   | NO_LIMIT     | 0       | Err(1) |
| 1  | 0  | 20 | 0      | 0      | 256      | Safe      | false   | NO_LIMIT     | 0       | Err(2) |
| 1  | 5  | 5  | 0      | 0      | 256      | Safe      | false   | NO_LIMIT     | 0       | Err(3) |
| 1  | 2  | 20 | 19     | 0      | 256      | Safe      | false   | NO_LIMIT     | 0       | Err(4) |
| 1  | 2  | 20 | 20     | 20     | 256      | Safe      | false   | NO_LIMIT     | 0       | Err(5) |
| 1  | 2  | 20 | 20     | 21     | 256      | Safe      | false   | NO_LIMIT     | 0       | Ok     |
| 1  | 2  | 20 | 0      | 0      | 0        | Safe      | false   | NO_LIMIT     | 0       | Err(6) |
| 1  | 2  | 20 | 0      | 0      | 256      | LeaseBased| false   | NO_LIMIT     | 0       | Err(7) |
| 1  | 2  | 20 | 0      | 0      | 256      | LeaseBased| true    | NO_LIMIT     | 0       | Ok     |
| 1  | 2  | 20 | 0      | 0      | 256      | Safe      | false   | 0            | 100     | Err(8) |

---

## Inferred intent

The validation is a precondition gate that prevents obviously wrong configurations
from starting a Raft node. Separating validation from the `Config` constructor
allows library users to build configs incrementally and validate once.

The default values are designed so `Config::new(id)` with a valid `id > 0` is
*valid by default* — users only need to change fields if they want non-default behaviour.

The ordering of checks (ID → heartbeat → election → election range → inflight → lease → size)
reflects roughly descending severity/obviousness of the error.

---

## Open questions

1. Should `max_election_tick = 1` (or `2`) while `election_tick = 10` be accepted? The check `min < max` after canonicalisation allows this — is that intentional?
2. Is `max_uncommitted_size = max_size_per_msg` (equality) intentional? The error message says "greater than" but the check is `<` (allowing equality).

---

*Lean Squad — Task 2 informal spec for `config_validate`.*
