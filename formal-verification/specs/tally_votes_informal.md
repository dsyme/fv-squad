# Informal Specification: `tally_votes` and `has_quorum`

**Source**: `src/tracker.rs` — `ProgressTracker::tally_votes` and `ProgressTracker::has_quorum`

🔬 *Lean Squad — auto-generated informal specification.*

---

## 1. `tally_votes`

### Purpose

`tally_votes` scans the `votes` map (from node ID → `bool`) and counts how many voter-members
of the current configuration have voted "yes" (`granted`) and how many have voted "no"
(`rejected`). It then delegates to `vote_result` to determine the overall election outcome.
Non-voter entries in the `votes` map are silently ignored.

### Preconditions

- `self.conf.voters` is a valid quorum configuration (a `JointConfig` with one or two
  majority configs).
- `self.votes` is a `HashMap<u64, bool>` that may contain votes from nodes not currently
  in the voter set (e.g., stale or pre-configuration-change entries).

### Postconditions

- `granted` = number of distinct voter IDs in `self.conf.voters` that mapped to `true`
  in `self.votes`.
- `rejected` = number of distinct voter IDs in `self.conf.voters` that mapped to `false`
  in `self.votes`.
- `granted + rejected ≤ |voters|`  — **key safety bound**: total observed votes can never
  exceed the voter population.
- The returned `VoteResult` equals what `self.vote_result(&self.votes)` would return
  independently (consistency invariant).

### Invariants

- Votes from non-voter IDs do not affect `granted` or `rejected`.
- `granted ≥ 0`, `rejected ≥ 0` (obvious in Lean's Nat but worth stating).

### Edge Cases

- **Empty voter set**: `granted = 0`, `rejected = 0`, and `VoteResult::Won` (by convention).
- **No votes cast**: `granted = 0`, `rejected = 0`, result is `Pending` (if voters ≠ ∅).
- **All voters voted yes**: `granted = |voters|`, `rejected = 0`, result is `Won`.
- **All voters voted no**: `granted = 0`, `rejected = |voters|`, result is `Lost`.
- **Votes from non-members**: do not affect granted/rejected counts.

### Examples

| voters | votes map          | granted | rejected | result  |
|--------|--------------------|---------|----------|---------|
| {1,2,3}| {1→true,2→true}   | 2       | 0        | Won     |
| {1,2,3}| {1→false,2→false} | 0       | 2        | Lost    |
| {1,2,3}| {1→true}           | 1       | 0        | Pending |
| {1,2,3}| {}                 | 0       | 0        | Pending |
| {}     | anything           | 0       | 0        | Won     |

### Inferred Intent

The comment in the Rust code explicitly states: "Make sure to populate granted/rejected
correctly even if the Votes slice contains members no longer part of the configuration.
This doesn't really matter in the way the numbers are used (they're informational), but
might as well get it right." — the counts are for **display purposes**; the actual election
outcome is determined by `vote_result`, which also filters by voter membership.

### Open Questions

- None identified — the spec is clear and the code matches the comment.

---

## 2. `has_quorum`

### Purpose

`has_quorum(potential_quorum)` determines whether the given set of node IDs forms a quorum
in the current voter configuration. It does this by calling `vote_result` with a synthetic
vote assignment that returns `Some(true)` for nodes in `potential_quorum` and `None` for
all others, then checking if the result is `Won`.

### Preconditions

- `self.conf.voters` is a valid quorum configuration.
- `potential_quorum` is an arbitrary `HashSet<u64>`.

### Postconditions

- Returns `true` iff `vote_result(|id| if id ∈ potential_quorum { Some(true) } else { None }) == Won`.
- Equivalently (for simple non-joint config): `|potential_quorum ∩ voters| ≥ majority(|voters|)`.

### Invariants

- **Superset closure**: if `S` is a quorum and `T ⊇ S`, then `T` is also a quorum.
- **Empty set**: `has_quorum(∅) = false` unless `voters = ∅`.
- **Full set**: `has_quorum(voters) = true` whenever `voters ≠ ∅`.
- **Empty voter config**: always returns `true` (by the empty-config convention in `vote_result`).

### Edge Cases

- **Empty `potential_quorum`**: quorum requires ≥1 yes vote, so returns `false` (unless `voters = ∅`).
- **Empty voter config**: `vote_result` of an empty config is `Won`, so returns `true`.
- **Singleton voter config**: `potential_quorum` must contain the single voter.

### Examples

| voters | potential_quorum | has_quorum? |
|--------|------------------|-------------|
| {1,2,3}| {1,2}            | true        |
| {1,2,3}| {1}              | false       |
| {1,2,3}| {}               | false       |
| {}     | anything         | true        |
| {1}    | {1}              | true        |
| {1}    | {}               | false       |

### Open Questions

- The Rust code uses `JointConfig::vote_result` which handles two-phase (joint) configs.
  The Lean spec simplifies to the single-phase case (normal operation). The joint-quorum
  behaviour is already verified in `JointQuorum.lean`.
