# Informal Specification: `ProgressTracker::has_quorum`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

## Purpose

`ProgressTracker::has_quorum(potential_quorum: &HashSet<u64>) -> bool` determines whether a
given set of node IDs contains a strict majority of the current voter configuration.

This is the **only correct way** to check whether a quorum exists for the whole group
(per the doc comment in `src/tracker.rs:357`). Callers must not iterate over `progress`
directly and count manually, as the cluster may be mid-transition with two quorum configs
active simultaneously (joint configuration).

## Source

`src/tracker.rs:357–362`

```rust
pub fn has_quorum(&self, potential_quorum: &HashSet<u64>) -> bool {
    self.conf
        .voters
        .vote_result(|id| potential_quorum.get(&id).map(|_| true))
        == VoteResult::Won
}
```

## Algorithm

1. For each voter ID in `self.conf.voters`, check if it is in `potential_quorum`.
   - If present: map to `Some(true)` (yes vote).
   - If absent: map to `None` (not voted / absent).
2. Pass this check function to `self.conf.voters.vote_result(...)`.
3. Return `true` iff the result is `VoteResult::Won`.

The `vote_result` function (majority quorum variant) computes:
- `yes_count = |{v ∈ voters | v ∈ potential_quorum}|`
- `q = majority(|voters|) = |voters|/2 + 1`
- Returns `Won` if `yes_count ≥ q`, otherwise `Pending` or `Lost`.

Special case: if the voter set is empty, `vote_result` returns `Won` unconditionally, so
`has_quorum` returns `true` for any `potential_quorum` when `voters` is empty.

## Preconditions

- `self.conf` is a valid `Configuration` (may include a joint outgoing config).
- `potential_quorum` is any `HashSet<u64>` — typically a subset of peer node IDs.

## Postconditions

- Returns `true` iff `|voters ∩ potential_quorum| ≥ majority(|voters|)` OR `voters` is empty.
- Returns `false` otherwise.

## Invariants

**Quorum intersection (Raft safety property)**: For any two sets A and B, if
`has_quorum(A) = true` and `has_quorum(B) = true` and `voters ≠ []`, then
`A ∩ B ∩ voters ≠ ∅`.

That is, no two disjoint sets can simultaneously form a quorum for the same voter
configuration. This is the mathematical foundation of Raft's leader-uniqueness guarantee.

**Monotonicity**: If `has_quorum(A) = true` and `A ⊆ B`, then `has_quorum(B) = true`.

## Edge Cases

- **Empty voter set**: returns `true` for any input (convention for joint quorum
  compatibility — a no-voter config vacuously satisfies any quorum requirement).
- **Singleton voter set**: returns `true` iff the sole voter is in `potential_quorum`.
- **Empty `potential_quorum`**: returns `false` unless `voters` is also empty.
- **`potential_quorum` ⊇ voters**: always returns `true` (trivially forms quorum).
- **`potential_quorum` contains non-voter IDs**: these are ignored — only voters count.

## Examples

| `voters`     | `potential_quorum` | `majority` | `overlap` | Result  |
|--------------|--------------------|-----------|-----------|---------|
| `[]`         | `{}`               | n/a       | 0         | `true`  |
| `[1]`        | `{1}`              | 1         | 1         | `true`  |
| `[1]`        | `{2}`              | 1         | 0         | `false` |
| `[1, 2, 3]`  | `{1, 2}`           | 2         | 2         | `true`  |
| `[1, 2, 3]`  | `{3}`              | 2         | 1         | `false` |
| `[1,2,3,4]`  | `{1, 2, 3}`        | 3         | 3         | `true`  |
| `[1,2,3,4]`  | `{1, 2}`           | 3         | 2         | `false` |

## Inferred Intent

The function is designed as the single authoritative quorum check, delegating to
`JointConfig::vote_result`. This ensures that during configuration transitions (where
the cluster operates under a joint quorum requiring majorities in both old and new configs),
callers do not accidentally use a single-config majority check.

The `quorum_recently_active` function (lines 336–352) uses `has_quorum` as its final step:
it builds a set of recently-active nodes (including the leader itself), then asks `has_quorum`
whether that set forms a quorum.

## Open Questions

1. **Joint configuration**: The formal model in `HasQuorum.lean` uses a single `List Nat`
   for `voters`. The Rust `has_quorum` delegates to `JointConfig::vote_result`, which handles
   joint configs (two concurrent quorum configs). Does the quorum intersection property hold
   for joint quorums? (Joint quorum requires majority in BOTH configs — a stricter requirement
   that implies the same intersection guarantee, but with a different proof.)

2. **Leader inclusion in `quorum_recently_active`**: The function adds `perspective_of` to
   `active` unconditionally (line 342). Is this necessary for the quorum to succeed, or just
   an optimisation? A theorem relating `quorum_recently_active` to `has_quorum` and `Progress`
   state would clarify this.
