# FV Proof Utility Critique

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

## Last Updated
- **Date**: 2026-03-27 13:54 UTC
- **Commit**: `52eb13408ac52e43bf86291953239b7d790236d9`

---

## Overall Assessment

Formal verification coverage has advanced to **91 theorems proved across 6 functions, with
0 `sorry` remaining**.  The quorum subsystem is fully specified and proved
(`vote_result`, `committed_index`, and their joint-config variants), and log-layer coverage
has now begun: all 12 key correctness theorems for `RaftLog::find_conflict` are proved.
The remaining gap is that the log operations beyond `find_conflict` (`maybe_append`,
`append_entry`, `commit_to`) and the downstream state-machine (`progress`, `inflights`) are
untouched, so no end-to-end Raft correctness theorem exists yet.  The next natural target
is `RaftLog::maybe_append`, which calls `find_conflict` and whose specification can build
directly on the `FindConflict` theorems.

---

## Proved Theorems

### `LimitSize.lean` — 17 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `totalSize_take_le` | Low (helper) | Low | Auxiliary bound; supports higher-level proofs |
| `limitSizeCount_ge_k` | Low (helper) | Low | Internal monotone count bound |
| `limitSizeCount_le_add_length` | Low (helper) | Low | Count bounded by list length |
| `limitSizeCount_pos` | Low (helper) | Low | Count is always ≥ 1 |
| `limitSizeCount_le_length` | Low (helper) | Low | Count ≤ length |
| `limitSize_is_prefix` | Mid | **High** | Would catch any code that deleted from the wrong end, permuted, or inserted extra entries |
| `limitSize_nonempty` | Mid | **High** | Would catch logic that truncated to 0 entries (protocol violation: must send ≥ 1 entry) |
| `limitSize_none` | Mid | Medium | No-op under `None` budget; catches overly aggressive truncation |
| `limitSize_le_one` | Mid | Medium | Handles 0-or-1-element edge cases correctly |
| `limitSize_nil` | Mid | Low | Nil input stays nil — degenerate case, unlikely to be a real bug |
| `limitSize_singleton` | Mid | Medium | Single-element stays intact under any budget |
| `limitSize_length_le` | Mid | Medium | Result is never longer than input |
| `limitSize_length_pos` | Mid | **High** | Guarantees non-empty output when input was non-empty |
| `limitSize_size_bound` | Mid | **High** | Total serialised size respects the budget — core correctness property |
| `limitSize_maximality` | High | **High** | Adding one more entry would exceed the budget — output is *maximal*, not just valid |
| `limitSize_idempotent` | Mid | **High** | Applying twice is a no-op — catches implementations that behave differently on already-truncated input |
| `limitSize_prefix_of_prefix` | Mid | Medium | Prefix of a prefix is still a prefix under tightened budget |

**Assessment**: The 5 helper theorems are low-value individually but necessary scaffolding.
The 12 main theorems cover the key correctness criteria well.  `limitSize_maximality` is
particularly valuable: it proves the output is *optimal* (no larger prefix would fit), not
just *safe* (fits within budget).  This is the strongest and rarest kind of correctness
guarantee.

---

### `ConfigValidate.lean` — 10 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `configValidate_iff_valid` | Mid | **High** | Boolean fn ↔ propositional predicate — ensures all 8 constraints are captured |
| `config_valid_id` | Low | Medium | `id ≠ 0` constraint isolation |
| `config_valid_heartbeat` | Low | Medium | `heartbeat_tick > 0` |
| `config_valid_election` | Low | Medium | `election_tick > heartbeat_tick` |
| `config_valid_min_election` | Low | Medium | `min_election_tick ≥ election_tick` (when non-zero) |
| `config_valid_max_election` | Low | Medium | `max_election_tick > min_election_tick` |
| `config_valid_inflight` | Low | Medium | `max_inflight_msgs > 0` |
| `config_valid_lease` | Low | Medium | `LeaseBased → check_quorum` |
| `config_valid_uncommitted` | Low | Medium | `max_uncommitted_size ≥ max_size_per_msg` |
| `configValidate_false_on_invalid` | Mid | Medium | Sanity check: invalid config returns `false` |

**Assessment**: The 9 constraint-decomposition theorems are individually low-level but
collectively valuable as a machine-checked regression guard: if any constraint were
accidentally deleted from `validate()`, at least one theorem would fail.  The
`configValidate_iff_valid` theorem is the most useful single result — it ensures the
boolean function is *equivalent* to the full conjunctive specification.

**Concern**: The `Config.valid` predicate is defined in Lean and may not track future
changes to `Config::validate` in Rust.  There is no automated check that the Lean `Config`
struct includes all fields checked by the Rust function.  A maintainer adding a new
validation constraint to Rust would need to manually update the Lean model.

---

### `MajorityVote.lean` — 21 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `majority_pos` / `majority_always_pos` | Low | Low | `majority n ≥ 1` — structural property |
| `majority_gt_half` / `majority_exceeds_half` | Low | Medium | `n/2 < majority n` — correctness of the majority threshold |
| `majority_monotone` | Low | Medium | Larger group → larger majority requirement |
| `yesCount_le_length` | Low | Low | Count bounded by voter set size |
| `missingCount_le_length` | Low | Low | Missing-vote count bounded by size |
| `yesCount_add_missing_le` | Low | Low | Yes + missing ≤ total |
| `yesCount_all_yes` | Low | Low | All-yes gives full count |
| `voteResult_empty_is_Won` | Mid | Medium | Empty config vacuously wins — expected degenerate behaviour |
| `voteResult_Won_iff` | High | **High** | Won iff yes ≥ majority — core quorum threshold characterisation |
| `voteResult_Lost_iff` | High | **High** | Lost iff missing < majority — necessary condition for knowing result won't change |
| `voteResult_Pending_iff` | High | **High** | Pending otherwise — guarantees exhaustiveness of case analysis |
| `voteResult_exhaustive` | High | **High** | Every configuration of votes produces exactly one of Won/Pending/Lost |
| `single_yes_wins` | Mid | Medium | One-voter quorum wins with yes |
| `voteResult_all_yes` | Mid | Medium | All-yes → Won |
| `voteResult_not_Won_of_few_yes` | Mid | Medium | Too few yes votes cannot win |
| `voteResult_not_Lost_of_optimistic` | Mid | Medium | Enough possible-yes cannot lose |
| `voteResult_majority_yes_wins` | Mid | Medium | Majority yes → Won (redundant with Won_iff but readable spec) |
| `voteResult_count_bound` | Low | Low | Count bounds |
| `voteResult_yes_bound` | Low | Low | Yes-count ≤ total |

**Assessment**: The three `_iff` characterisation theorems (`Won_iff`, `Lost_iff`,
`Pending_iff`) together with `voteResult_exhaustive` are the most valuable results.  They
give a *complete* characterisation of `vote_result`: every possible vote configuration maps
to exactly one outcome, and the threshold for each outcome is pinned precisely.  These
theorems would catch: wrong majority formula, off-by-one in quorum threshold, any case
where the result could be both Won and Lost simultaneously.

---

### `JointVote.lean` — 14 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `combineVotes_Won_iff` | Mid | **High** | Joint Won requires both to Win |
| `combineVotes_Lost_iff` | Mid | **High** | Joint Lost if either Loses |
| `combineVotes_Pending_iff` | Mid | **High** | Joint Pending otherwise |
| `combineVotes_symm_Lost` | Low | Medium | Lost is symmetric in the combiner |
| `jointVoteResult_Won_iff` | High | **High** | Joint quorum requires both sub-quorums to win |
| `jointVoteResult_Lost_iff` | High | **High** | Either losing sub-quorum causes a Loss |
| `jointVoteResult_Pending_iff` | High | **High** | Pending otherwise — exhaustiveness |
| `jointVoteResult_non_joint` | High | **High** | Non-joint (empty outgoing) degenerates to single quorum |
| `jointVoteResult_incoming_Lost` | Mid | **High** | If incoming Loses, joint result Loses |
| `jointVoteResult_outgoing_Lost` | Mid | **High** | If outgoing Loses, joint result Loses |
| `jointVoteResult_all_yes` | Mid | Medium | All-yes → joint Won |
| `jointVoteResult_exhaustive` | High | **High** | Complete characterisation — no undefined result |
| `jointVoteResult_Won_symm` | Mid | Medium | Won is symmetric: `(inc, out)` ≡ `(out, inc)` |
| `jointVoteResult_Lost_symm` | Mid | Medium | Lost is symmetric |

**Assessment**: `jointVoteResult_non_joint` (`J4`) is a particularly important correctness
property: it proves that when transitioning from joint back to single-config, the quorum
rule collapses correctly to the single-config rule.  This is exactly the kind of subtle
protocol edge case where bugs lurk.  The symmetry theorems (J9, J10) have no direct Rust
counterpart but serve as sanity checks on the model.

---

### `CommittedIndex.lean` — 17 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `sortDesc_length` | Low | Low | Sort preserves length |
| `sortDesc_perm` | Low | Low | Sort is a permutation of input |
| `sortDesc_pairwise` | Low | Medium | Sort produces descending order — validates the sort direction |
| `sortedAcked_length` | Low | Low | Mapped-and-sorted list has same length as voter set |
| `sortedAcked_perm` | Low | Low | `sortedAcked` is a permutation of `map acked voters` |
| `committedIndex_empty` | Low | Medium | Empty config returns 0 (Lean) / MAX (Rust) — documents divergence |
| `committedIndex_empty_contract` | Low | Medium | Lean 0 ≤ any bound — ensures callers can use the empty result |
| `committedIndex_singleton` | Mid | Medium | Single voter: committed = acked index |
| `countGe_zero` | Low | Low | Count ≥ 0 — trivial |
| `filter_ge_sublist` | Low | Low | Filter monotone in threshold |
| `countGe_antitone` | Mid | Medium | Higher threshold → smaller count |
| `countGe_perm` | Low | Low | Count invariant under permutation |
| `countGe_eq_countGeList` | Mid | Medium | `countGe` agrees with `filter`-based count on sorted list |
| `committedIndex_all_zero` | Mid | Medium | All-zero acked → committed index is 0 |
| `committedIndex_safety` | **High** | **Very High** | ≥ majority voters have acked ≥ ci — *core Raft safety property* |
| `committedIndex_maximality` | **High** | **Very High** | No larger index has a majority ack — *optimality* |
| `committedIndex_mono` | **High** | **Very High** | Pointwise acked ↑ → committed index ↑ — *monotonicity / liveness* |

**Assessment**: The final three theorems (`committedIndex_safety`, `committedIndex_maximality`,
`committedIndex_mono`) are the highest-value results in the entire FV effort.  They directly
formalise the three key correctness criteria for the sort-then-index algorithm:
- **Safety**: the result is always safe to commit (a majority has acked it).
- **Maximality**: the result is the *best* safe choice (no one is leaving value on the table).
- **Monotonicity**: the committed index can only advance as acknowledgements arrive (a liveness precondition).

These would catch: wrong sort direction, wrong majority index (off-by-one), wrong acked
function, any regression that caused committed index to go backwards.  The 9 helper
theorems are necessary scaffolding; they are not individually interesting but their
correctness is required for the high-level proofs to go through.

---

### `FindConflict.lean` — 12 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `findConflict_empty` (FC1) | Low | Low | Empty input → 0; trivial boundary case |
| `findConflict_head_mismatch` (FC2) | Low | Medium | Head mismatch → return head index immediately |
| `findConflict_head_match` (FC3) | Low | Medium | Head match → recurse into tail |
| `findConflict_zero_of_all_match` (FC4a) | Mid | **High** | All entries match → result is 0 (no truncation needed) |
| `findConflict_all_match_of_zero` (FC4b) | Mid | **High** | Result 0 + positive indices → all entries match (converse) |
| `findConflict_nonzero_witness` (FC5+FC6) | Mid | **High** | Non-zero result → witnessing entry exists with that index and a term mismatch |
| `findConflict_first_mismatch` (FC7) | **High** | **Very High** | First-mismatch characterisation: all `pre` match, `e` mismatches → returns `e.index` |
| `findConflict_skip_match_prefix` (FC8) | Mid | **High** | Matching prefix is transparent — result depends only on the suffix after the prefix |
| `findConflict_singleton_match` (FC9) | Low | Low | Single matching entry → 0 |
| `findConflict_singleton_mismatch` (FC10) | Low | Low | Single mismatching entry → that entry's index |
| `findConflict_zero_iff_all_match` (FC11) | **High** | **Very High** | Biconditional: zero ↔ all match (for positive-index entries) — combines FC4a + FC4b |
| `findConflict_result_in_indices` (FC12) | Mid | Medium | Non-zero result is always the index of some entry in the input |

**Assessment**: `findConflict_zero_iff_all_match` (FC11) and `findConflict_first_mismatch`
(FC7) are the most valuable results.  FC11 establishes the central "no conflict detected ↔
all entries agree with the log" equivalence — the exact correctness criterion a Raft
implementation needs.  FC7 proves the output is the *first* mismatch index, not an
arbitrary one: this would catch any implementation that skips entries, re-orders the scan,
or returns the wrong index upon detecting a conflict.  The positive-index precondition in
FC4b and FC11 accurately documents the protocol assumption that index 0 is only used as a
sentinel return value, not as a real log position.

---

## Gaps and Recommendations

Prioritised by impact:

### 1. `JointConfig::committed_index` — **High priority** *(phase 3 — Lean spec written; awaiting reprovement after branch loss)*

`src/quorum/joint.rs` `committed_index` is simply `min(incoming.committed_index(acked),
outgoing.committed_index(acked))` (with the Rust empty-→-MAX divergence handled).  All 14
theorems (safety, maximality, monotonicity for incoming/outgoing quorums, joint safety,
joint maximality) were proved in a prior run but the PR was not merged.  This is the
highest-priority target to recover and resubmit.  The `empty→MAX` Rust divergence is the
main subtlety.

### 2. `RaftLog::maybe_append` — **High priority** *(phase 1, depends on `find_conflict` — now done)*

Calls `find_conflict`, then truncates and appends.  Key properties: log suffix is replaced
only after the conflict point; log never shrinks if there is no conflict; the output log
has the same prefix up to the conflict index.  The `FindConflict` theorems (especially FC7
and FC11) provide the key building blocks — this is the natural next step.

### 3. `Inflights` ring buffer — **Medium priority** *(phase 1)*

`src/tracker/inflights.rs` implements a ring buffer of in-flight message counts.
Key invariants: `add` does not lose elements; `free_to` advances the buffer correctly;
the count never exceeds capacity.  Ring buffer invariants are the kind of property
where bugs hide in index arithmetic — FV would add real value here.

### 4. Bridging theorem for `committedIndex_empty` — **Low priority**

The `committedIndex_empty_contract` theorem documents that the Lean model returns `0`
where Rust returns `u64::MAX`, but does not prove a bridging equivalence for joint-quorum
callers.  Once `JointConfig::committed_index` is formalised, a theorem showing
`joint.committedIndex ≤ min(incoming.committedIndex, outgoing.committedIndex)` (with
appropriate handling of the 0/MAX difference) would close this gap.

### 5. Composition / end-to-end safety property — **Long-term goal**

No end-to-end Raft safety theorem exists yet (e.g., "two entries committed at the same
index by the same term are identical").  This requires composing proofs about the quorum
subsystem, the log, and the state machine.  It is a significant proof-engineering effort,
but the quorum proofs laid in this work provide the necessary quorum-safety building blocks.

---

## Known Concerns

### Concern 1: Voter-list type (List vs. Set)

All Lean models use `List Nat` for voter sets.  The Rust uses `HashSet<u64>`.  Duplicate
voters in a `List` would inflate vote counts and potentially break `voteResult_Won_iff`
(e.g., one physical voter voting twice).  The theorems are stated without a `Nodup`
precondition, which means they technically hold even with duplicates — but the semantics
are wrong for duplicated voters.

**Recommendation**: Add a `voters.Nodup` hypothesis to the `_iff` theorems, or add a
`List.dedup` normalisation step to the Lean model.  This is the most notable semantic gap
in the current models.

### Concern 2: Non-group-commit path only for `committed_index`

The Lean model covers only `use_group_commit = false`.  The group-commit path
(`majority.rs` lines 177–186) uses a different algorithm and is completely unverified.
If group-commit is ever enabled in practice, the Safety/Maximality guarantees do not apply.

### Concern 3: `u64` overflow not modelled

All numeric types are `Nat` in Lean.  Overflow scenarios (e.g., acked indices near
`u64::MAX`, extremely large voter counts) are not covered.  In practice these are
unreachable, but the gap is worth noting.

---

## Positive Findings

1. **`commitedIndex_safety` and `committedIndex_maximality`** are genuine discoveries:
   they required non-trivial proof engineering (order statistics on sorted lists,
   `countGe_eq_countGeList`, `pairwise_ge_antitone`) and confirm that the sort-then-index
   algorithm is provably correct.  These are the strongest results in the FV portfolio.

2. **`jointVoteResult_non_joint`** (J4) formalises a subtle protocol invariant — that
   joint quorum degenerates correctly to single quorum — that could easily hide a
   regression bug.  Having this proved mechanically is a genuine safety net.

3. **`limitSize_maximality`** proves optimality, not just safety.  This is unusual: most
   correctness proofs only verify that output satisfies constraints, not that it is the
   *best* output satisfying those constraints.  The maximality proof provides confidence
   that `limit_size` never produces unnecessarily small batches.

4. **`findConflict_zero_iff_all_match`** (FC11) provides a clean biconditional
   characterisation of the "no conflict" case, and **`findConflict_first_mismatch`** (FC7)
   pins down exactly *which* entry's index is returned.  Together they eliminate a whole
   class of subtle off-by-one bugs (returning the wrong conflict index, or returning a
   conflict index when none exists).

5. **No bugs found** in any of the six verified functions.  This is evidence (not proof)
   that the Raft quorum logic and the log-conflict scan as implemented are correct for the
   modelled paths.

---

> 🔬 Generated by [Lean Squad](https://github.com/dsyme/fv-squad/actions/runs/23649096928) automated formal verification.
