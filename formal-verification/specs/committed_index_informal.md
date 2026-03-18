# Informal Specification: `MajorityConfig::committed_index`

> 🔬 *Lean Squad — informal specification document for formal verification.*

**Target**: `MajorityConfig::committed_index`  
**File**: `src/quorum/majority.rs` (lines ~67–125)  
**Phase**: 2 — Informal Spec

---

## 1. Purpose

`committed_index` computes the **highest log index that is safe to commit** given the
acknowledged (matched) log indices of all voters in a majority quorum.

A log entry at index `i` is safe to commit when at least `majority(n)` of the `n` voters
have acknowledged (replicated) it — i.e., `i` is ≤ their `acked_index`. The function
returns the largest such `i` over the current voter set.

This is one of the most safety-critical computations in Raft: returning too large a value
could cause a leader to commit entries that are not yet replicated to a quorum, violating
the **Log Matching** and **Leader Completeness** invariants.

---

## 2. Inputs

| Parameter | Type | Description |
|-----------|------|-------------|
| `self.voters` | `HashSet<u64>` | Set of voter IDs in this majority configuration |
| `use_group_commit` | `bool` | Whether to apply the multi-group commit extension |
| `l` | `impl AckedIndexer` | Maps each voter ID to its acknowledged `Index` (or `None` if unknown) |

The `Index` struct has two fields:
- `index: u64` — the replicated log index (defaults to `0` if the voter is unknown).
- `group_id: u64` — the group the voter belongs to (0 means "no group" / group commit disabled for this voter).

---

## 3. Return Value

Returns `(committed_index: u64, group_commit_used: bool)`.

- `committed_index`: the highest safely committable log index.
- `group_commit_used`: `true` only when the group-commit path was taken and successfully found a cross-group quorum.

---

## 4. Algorithm (Non-Group-Commit Path)

When `use_group_commit` is `false`:

1. Collect the `acked_index` for every voter (`None` maps to `Index { index: 0, group_id: 0 }` via `unwrap_or_default()`).
2. Sort the collected indices in **descending** order (highest first).
3. Return `matched[majority(n) - 1].index` — the `(quorum-1)`th largest acknowledged index.

**Why this works**: after sorting descending, at index `majority(n) - 1` there are exactly
`majority(n)` voters with an acknowledged index ≥ that value. This is the definition of
"safely committed by a majority".

**Example** (from the doc-comment): indices `[2, 2, 2, 4, 5]` → sorted descending → `[5, 4, 2, 2, 2]`, `majority(5) = 3`, `matched[2] = 2`. Returns `2`.

---

## 5. Algorithm (Group-Commit Path)

When `use_group_commit` is `true`, a stricter commit index is computed that ensures no
single group can alone constitute a quorum. The intent is to ensure cross-datacenter or
cross-rack replication before committing.

After sorting descending:

1. Start with `quorum_commit_index = matched[majority(n) - 1].index` (same as non-group path).
2. Scan the sorted array looking for the first voter whose `group_id` differs from the
   leading non-zero `group_id`.
3. **Observations during scan**:
   - If `group_id == 0`: mark that not all voters are in a group (`single_group = false`), but continue.
   - If `checked_group_id == 0`: record the first non-zero group seen.
   - If `checked_group_id == m.group_id`: same group, continue.
   - If `checked_group_id != m.group_id` (and neither is 0): a cross-group boundary is found. Return `(min(m.index, quorum_commit_index), true)`.
4. After scanning:
   - If `single_group = true` (all voters have the same non-zero group_id): group commit did not apply — return `(quorum_commit_index, false)`.
   - Else (some voters had `group_id == 0`): return `(matched.last().unwrap().index, false)` — the **minimum** acknowledged index across all voters.

**Example** (from doc-comment): `[(1, group=1), (2, group=2), (3, group=2)]` sorted descending by index → `[(3, 2), (2, 2), (1, 1)]`. `quorum = majority(3) = 2`. `quorum_index = (2, 2)`. Scan: first entry `(3, 2)`: `checked_group_id = 2`. Second `(2, 2)`: same group. Third `(1, 1)`: different group → return `(min(1, 2), true) = (1, true)`.

---

## 6. Postconditions

### Non-group-commit

Let `matched_indices` be the multiset `{ l.acked_index(v).unwrap_or_default().index | v ∈ voters }`.

- **Committed index is achievable by a quorum**:  
  `|{ v ∈ voters | l.acked_index(v).unwrap_or_default().index ≥ committed_index }| ≥ majority(|voters|)`
  
- **Committed index is the maximum such value**:  
  `committed_index` is the largest `k` such that at least `majority(|voters|)` voters have `acked_index ≥ k`.

- **Lower bounded by 0**: `committed_index ≥ 0`.

- **Upper bounded by the maximum acked index**: `committed_index ≤ max(matched_indices)`.

- **`group_commit_used = false`** always when `use_group_commit = false`.

### Empty config

`committed_index(_, _) = (u64::MAX, true)` — the empty config returns the highest possible
index, allowing joint quorums with one empty half to be governed entirely by the non-empty half.

### Monotonicity (key safety property)

If every voter's `acked_index` is non-decreasing (logs only grow), then
`committed_index` is non-decreasing over time. This ensures Raft never "uncommits" an entry.

---

## 7. Invariants

1. **Safety**: `committed_index ≤ acked_index(v)` for at least `majority(n)` voters `v`.
2. **Maximality** (non-group path): no larger index satisfies the safety property.
3. **Monotonicity**: as `acked_index` values grow, `committed_index` grows (or stays the same).
4. **Empty config convention**: returns `u64::MAX` so that `min(empty_result, other_result) = other_result` in joint quorums.

---

## 8. Edge Cases

| Scenario | Expected result |
|----------|----------------|
| Empty voter set | `(u64::MAX, true)` |
| 1 voter, acked index 5 | `(5, false)` |
| 1 voter, acked index unknown (None) | `(0, false)` |
| 3 voters, indices `[5, 3, 1]` | `(3, false)` — `majority(3)=2`, `sorted[1]=3` |
| 3 voters, indices `[2, 2, 2]` | `(2, false)` |
| 5 voters, indices `[5, 4, 3, 2, 1]` | `(3, false)` — `majority(5)=3`, `sorted[2]=3` |
| 5 voters, all None | `(0, false)` |
| Group commit: two groups present | min of quorum-index and first cross-group index |
| Group commit: single group only | `(quorum_index, false)` |
| Group commit: some group_id=0 | `(min_of_all_matched_indices, false)` |

---

## 9. Stack vs. Heap Allocation

The implementation uses a fixed 7-element stack array for small voter sets (≤ 7 voters) and
allocates a heap `Vec` for larger sets. This is a **performance optimisation only** and does
not affect the algorithm's correctness. The formal model can ignore this and use a list/array.

---

## 10. Open Questions for Maintainers

1. **Group commit semantics**: the group commit algorithm is subtle. The spec above is
   derived from the code, but the *intended* semantics of the second return value (`false`)
   when all voters share a group ID (or some have `group_id=0`) is unclear. Is `false`
   meaning "group commit did not contribute"? Should callers treat `(result, false)` differently?

2. **`group_id = 0` meaning**: the code treats `group_id = 0` as "not in any group" and
   falls back to `matched.last().unwrap().index` (the minimum). Is this correct for all
   use cases? Could a voter legitimately be assigned to group 0?

3. **`u64::MAX` for empty config**: the sentinel value `u64::MAX` is used for the empty
   config return. Is there any caller that does not take `min(i, j)` of two config results
   where one might be empty? If not, the invariant is safe, but worth documenting.

4. **`unwrap_or_default()` for unknown voters**: voters not in the `AckedIndexer` are
   assigned `index = 0`. This is conservative (they are treated as having replicated nothing),
   but could mask bugs where a voter is in the config but missing from the indexer.

---

## 11. Relation to Raft Safety

`committed_index` is used directly in the `maybe_commit` path to advance the commit index.
Its correctness is essential for:

- **Log Matching**: committed entries must be identical on all future leaders.
- **Leader Completeness**: every committed entry must appear in the logs of all future leaders.

Verifying the non-group-commit path in Lean would give machine-checked evidence that the
quorum-based commit computation correctly identifies the maximum safely-committable index.
