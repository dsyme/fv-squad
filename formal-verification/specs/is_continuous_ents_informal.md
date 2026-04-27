# `is_continuous_ents` Informal Specification

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Function

`is_continuous_ents(msg: &Message, ents: &[Entry]) -> bool`  
Source: `src/util.rs`

## Purpose

Checks that a second batch of log entries `ents` immediately follows the last entry in
`msg.entries`, so that the two slices can be concatenated to form a contiguous log
segment without a gap or overlap.

This predicate is used when receiving a partial AppendEntries response: a follower may
have already buffered part of the message entries (`msg.entries`), and `ents` are the
remaining entries that are delivered asynchronously.  The guard ensures that the union
`msg.entries ++ ents` is still a contiguous log segment.

## Preconditions

None — the function is total and well-defined on all inputs.

## Postconditions / Return Value Semantics

Let `M = msg.entries` and `E = ents`.

| Condition | Return value |
|-----------|-------------|
| `M` is empty | `true` (vacuously continuous; nothing to append after) |
| `E` is empty | `true` (nothing to append; trivially OK) |
| Both non-empty | `true` iff `last(M).index + 1 = first(E).index` |

Equivalently, `is_continuous_ents(msg, ents) = M.is_empty() ∨ E.is_empty() ∨ (last(M).index + 1 = first(E).index)`.

## Invariants

- The function is **monotone in the vacuous cases**: if either slice is empty, the result
  is always `true`.
- When both slices are non-empty: the result depends **only** on `last(M).index` and
  `first(E).index`; all other entries are irrelevant.
- If `is_continuous_ents(msg, ents) = true` and both are non-empty, then
  `msg.entries ++ ents` has contiguous indices: entry `i` in the combined slice has index
  `first(M).index + i` (assuming M itself is well-formed).
- The predicate is **not** symmetric: `is_continuous_ents(msg_A, ents_B)` ≠
  `is_continuous_ents(msg_B, ents_A)` in general.

## Edge Cases

| Case | Outcome | Notes |
|------|---------|-------|
| `M = []`, `E = []` | `true` | Both empty |
| `M = []`, `E ≠ []` | `true` | No prior entries to extend |
| `M ≠ []`, `E = []` | `true` | Nothing to append |
| `last(M).index + 1 = first(E).index` | `true` | Perfect continuation |
| `last(M).index + 1 < first(E).index` | `false` | Gap: missing entries |
| `last(M).index + 1 > first(E).index` | `false` | Overlap: redundant entries |
| Single-entry `M` and single-entry `E` with consecutive indices | `true` | |

## Examples

| `M` indices | `E` indices | Result | Reason |
|-------------|-------------|--------|--------|
| `[]` | `[1,2,3]` | `true` | M empty |
| `[1,2,3]` | `[]` | `true` | E empty |
| `[1,2,3]` | `[4,5]` | `true` | `3+1=4` |
| `[1,2,3]` | `[5,6]` | `false` | Gap: `3+1=4≠5` |
| `[1,2,3]` | `[3,4]` | `false` | Overlap: `3+1=4≠3` |

## Inferred Intent

The function is a lightweight **boundary check** — it asserts that `ents` continues
exactly where `msg.entries` left off, with no entries missing and no entries duplicated.
It is used as a guard before merging buffered and newly-arrived entries to ensure the
assembled entry slice remains a valid contiguous log segment.

## Open Questions

1. Is `M` guaranteed to be internally contiguous (i.e., is `M[i].index = M[0].index + i`
   for all `i`)? The spec only reads `last(M).index`; if `M` itself has gaps, the predicate
   may pass even when the overall sequence has gaps elsewhere. The Rust code does not check
   this (it relies on callers to provide well-formed messages).
2. Should the function also check that `first(E).term` is compatible with `last(M).term`?
   Currently it checks only indices, not terms. A term check would strengthen the guard.
