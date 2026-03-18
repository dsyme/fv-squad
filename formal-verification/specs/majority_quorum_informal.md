# Informal Specification: `majority` and `MajorityConfig::vote_result`

> 🔬 *Lean Squad — informal specification document for formal verification.*

**Target**: `majority` utility function + `MajorityConfig::vote_result`  
**Files**: `src/util.rs` (line ~120), `src/quorum/majority.rs` (line ~100)  
**Phase**: 2 — Informal Spec

---

## 1. `majority(total: usize) -> usize`

### Purpose

Returns the minimum number of votes needed to constitute a majority among `total` voters. This is the quorum threshold used throughout Raft for elections and log commitment.

### Definition

```
majority(total) = (total / 2) + 1
```

(Integer division — rounds down before adding 1.)

### Preconditions

- `total` is a non-negative integer (`usize`).
- The implementation does not check for `total == 0`; callers generally ensure configurations have at least one voter. Behaviour with `total == 0` returns `1` (since `0/2 + 1 = 1`).

### Postconditions

- Returns a value strictly greater than `total / 2`.
- `majority(total) ≤ total` for all `total ≥ 1`.
- `majority(total) + majority(total) > total` — **any two majority sets must overlap** (the quorum intersection property, fundamental to Raft safety).

### Key Mathematical Properties

| Property | Statement |
|----------|-----------|
| Quorum threshold | `majority(n) * 2 > n` for all `n ≥ 1` |
| Non-zero | `majority(n) ≥ 1` for all `n ≥ 0` |
| Bounded | `majority(n) ≤ n` for all `n ≥ 1` |
| Monotone | `n ≤ m → majority(n) ≤ majority(m)` |
| Intersection | For any two sets `A, B ⊆ Voters` with `|A| ≥ majority(|Voters|)` and `|B| ≥ majority(|Voters|)`, `A ∩ B ≠ ∅` |

### Concrete Examples

| `total` | `majority(total)` |
|---------|------------------|
| 0 | 1 |
| 1 | 1 |
| 2 | 2 |
| 3 | 2 |
| 4 | 3 |
| 5 | 3 |
| 6 | 4 |
| 7 | 4 |

### Notes / Inferred Intent

- The function is declared `#[inline]` — it is a micro-utility called in hot paths.
- The naming of this function suggests that callers may also be interested in odd vs even cluster sizes; the formula is the standard "strict majority" threshold.
- The result is called `q` (for "quorum") inside `vote_result`.

---

## 2. `MajorityConfig::vote_result`

### Purpose

Given a set of voter IDs and a function `check: voter_id → Option<bool>` that maps each voter to their current vote (`Some(true)` = yes, `Some(false)` = no, `None` = not yet voted), determines whether the election result for this majority configuration is:
- `Won` — a quorum of yes votes has been reached,
- `Lost` — even counting all remaining voters as yes cannot reach quorum,
- `Pending` — neither quorum of yes nor definitive loss yet.

### Preconditions

- `self.voters` is a finite set of `u64` IDs.
- `check` is a pure total function from `u64` to `Option<bool>` (it may be called with IDs not in the voter set — but in practice it is only called for voter IDs).
- No precondition on number of voters. The empty set case is handled specially.

### Postconditions

- **Empty config** (`self.voters.is_empty()`): returns `Won`. By convention, an empty majority config always votes "won", enabling joint quorum configurations where one half is empty to behave like the non-empty half.

- **Won**: returned when the count of `Some(true)` responses is ≥ `majority(|voters|)`.

  Formally: `|{v ∈ voters | check(v) = Some(true)}| ≥ majority(|voters|)` → `Won`

- **Lost**: returned when even if all `None` voters voted yes, the total yes count would still fall short of majority.

  Formally: `|{v ∈ voters | check(v) = Some(true)}| + |{v ∈ voters | check(v) = None}| < majority(|voters|)` → `Lost`

- **Pending**: returned in all other cases — some uncertain votes could still tip the result either way.

### State Machine / Result Semantics

The three results form a progression:
```
    Pending → Won
    Pending → Lost
```
(Pending can only transition to Won or Lost, never the other way around. The function computes the current snapshot, not a transition.)

### Invariants / Correctness Criteria

1. **Completeness**: the three cases are exhaustive and mutually exclusive.
2. **Consistency with `majority`**: the result is `Won` iff `yes_count ≥ majority(n)`.
3. **Pessimism of `Lost`**: `Lost` is only returned when it is *impossible* for the vote to succeed even with optimistic future votes.
4. **Quorum safety**: if `Won` is returned, any other `Won` result from a concurrently computed majority over the same voter set must share at least one voter who voted `Some(true)` (this follows from the quorum intersection property).

### Edge Cases

| Scenario | Expected result |
|----------|----------------|
| All voters voted yes | `Won` |
| All voters voted no | `Lost` |
| All voters not yet voted | `Pending` |
| 1 voter, voted yes | `Won` |
| 1 voter, voted no | `Lost` |
| 1 voter, not voted | `Pending` |
| 0 voters | `Won` (special case) |
| 3 voters, 2 yes, 1 no | `Won` (2 ≥ majority(3) = 2) |
| 3 voters, 1 yes, 1 no, 1 pending | `Pending` (1 + 1 = 2 ≥ majority(3); 1 < 2) |
| 3 voters, 0 yes, 3 no | `Lost` (0 + 0 = 0 < 2) |
| 5 voters, 3 yes | `Won` |
| 5 voters, 2 yes, 0 no, 3 pending | `Pending` |
| 5 voters, 2 yes, 1 no, 2 pending | `Pending` (2+2=4 ≥ 3; but 2 < 3) |
| 5 voters, 2 yes, 3 no | `Lost` (2+0 < 3) |

### Open Questions for Maintainers

1. **`check` called with non-voter IDs**: The spec says `check` maps voters to votes, but the Rust signature accepts any `u64`. Should the spec guarantee `check` is only called with IDs in `self.voters`? (Currently it is — the loop iterates `self.voters`.)

2. **Semantics of `None`**: `None` is treated as "not yet voted" (optimistic — could still vote yes). Is this the intended semantics, or could `None` also represent an unreachable/crashed node? If the latter, the semantics of `Pending` vs `Lost` would change.

3. **Empty config wins**: Is the `Won` result for an empty config the correct semantic for all callers? In particular, does a two-phase (joint) configuration always have at least one non-empty half?

---

## Relation to Raft Safety

The `vote_result` function directly implements the Raft election safety invariant: a leader is elected only when a majority of nodes vote for it. Formally:

> **Election Safety**: at most one leader can be elected in any given term.

This holds because `Won` is only returned when a strict majority votes yes, and by the quorum intersection property (`majority(n) * 2 > n`), two candidates cannot both achieve a majority in the same term.

Verifying `vote_result` in Lean would give machine-checked confidence in this property for the Rust implementation.
