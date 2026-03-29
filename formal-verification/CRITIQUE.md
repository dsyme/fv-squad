# FV Proof Utility Critique

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

## Last Updated
- **Date**: 2026-03-29 17:10 UTC
- **Commit**: `3eea9f09d58b8aa4e9342db25a96eda4714951d1`

---

## Overall Assessment

Formal verification coverage has advanced to **147 theorems proved across 9 targets, with
0 `sorry` remaining**.  The quorum subsystem is comprehensively proved: `vote_result`,
`joint_vote_result`, `committed_index`, `joint_committed_index`, and `limit_size` are all
fully specified and verified, plus config validation.  Log-layer coverage now includes both
`find_conflict` (12 theorems) and `maybe_append` (18 theorems), with proofs reaching into
the implementation model: log-prefix preservation, suffix application, committed-index
monotonicity, and persisted-index rollback are all mechanically verified.  The ring-buffer
tracker (`inflights`) has 15 theorems in an open PR (phase 3), covering count/cap invariants,
`free_to` sortedness, and reset semantics.  The main remaining gap is that no end-to-end
Raft safety theorem exists yet — the state-machine level is untouched — and the `progress`
tracker and `append_entry`/`commit_to` log operations are unverified.

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

### `JointCommittedIndex.lean` — 10 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `jointCommittedIndex_le_in` (JCI1) | Low | Medium | Joint CI ≤ incoming CI — immediate from `Nat.min_le_left` |
| `jointCommittedIndex_le_out` (JCI2) | Low | Medium | Joint CI ≤ outgoing CI — immediate from `Nat.min_le_right` |
| `jointCommittedIndex_ge_lower_bound` (JCI3) | Mid | **High** | JCI is the *greatest* lower bound — characterises it as the min of the two CIs |
| `jointCommittedIndex_safety_in` (JCI4) | **High** | **Very High** | A majority of `incoming` have acked ≥ JCI — joint safety for incoming group |
| `jointCommittedIndex_safety_out` (JCI5) | **High** | **Very High** | A majority of `outgoing` have acked ≥ JCI — joint safety for outgoing group |
| `jointCommittedIndex_maximality` (JCI6) | **High** | **Very High** | Any k > JCI cannot be safely committed by at least one group — maximality |
| `jointCommittedIndex_mono` (JCI7) | High | **High** | Non-decreasing acked functions → non-decreasing joint CI — monotonicity |
| `jointCommittedIndex_all_zero` (JCI8) | Low | Low | All acks zero → joint CI zero |
| `jointCommittedIndex_empty_in` (JCI9) | Mid | Medium | Empty incoming → joint CI 0 (diverges from Rust's MAX, documented) |
| `jointCommittedIndex_empty_out` (JCI10) | Mid | Medium | Empty outgoing → joint CI 0 (diverges from Rust's MAX, documented) |

**Assessment**: JCI4–JCI6 are protocol-level safety and maximality theorems that directly
complement `CommittedIndex.lean`'s CI-Safety and CI-Maximality results.  Together they
prove that the *joint* committed index — used during Raft membership changes — retains the
same correctness guarantees as the single-group committed index.  JCI7 (monotonicity) is
essential for liveness arguments.  JCI9–JCI10 honestly document the known divergence where
the Lean model returns 0 for empty configs while Rust returns `u64::MAX`; callers must
account for this in any bridging theorem.

**Concern**: JCI9–JCI10 reveal that the Lean model of joint CI diverges from Rust when
either config group is empty — a state that arises during membership transitions.  Proofs
built on the joint CI model are valid only for non-empty configs on both sides (or must
explicitly handle the 0/MAX difference).  See CORRESPONDENCE.md §JointCommittedIndex for
the full divergence analysis.

---

### `MaybeAppend.lean` — 18 theorems (includes 2 helpers)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `maybeAppend_none` (MA1) | Mid | **High** | Returns `None` iff `match_term(idx,term)` fails — access-control gate |
| `maybeAppend_some` (MA2) | Mid | **High** | Returns `Some` iff `match_term` succeeds — converse of MA1 |
| `maybeAppend_conflict_eq` (MA3) | Mid | **High** | First component of `Some` is `findConflict(ents)` — conflict index identity |
| `maybeAppend_lastNew_eq` (MA4) | Mid | **High** | Second component is `idx + ents.length` — last new index identity |
| `maybeAppend_committed_eq` (MA5) | **High** | **Very High** | Committed advances to `max(s.committed, min(ca, lastNew))` — exact committed-index formula |
| `maybeAppend_committed_mono` (MA6) | High | **High** | Committed never decreases — monotonicity |
| `maybeAppend_committed_le_ca` (MA7) | High | **High** | Committed ≤ leader's `ca` — leader authority bound |
| `maybeAppend_committed_le_lastNew` (MA8) | High | **High** | Committed ≤ `lastNew` — cannot commit beyond appended entries |
| `maybeAppend_committed_eq_min` (MA9) | High | **High** | Exact min formula when committed was 0 — captures the base case |
| `maybeAppend_persisted_no_conflict` (MA10) | Mid | Medium | No conflict → `persisted` unchanged |
| `maybeAppend_persisted_rollback` (MA11) | Mid | **High** | Conflict at index c → `persisted` rolled back to `c - 1` when `persisted ≥ c` |
| `maybeAppend_persisted_preserved` (MA12) | Mid | Medium | `persisted < conflict` → `persisted` unchanged |
| `maybeAppend_log_prefix_preserved` (MA13) | **High** | **Very High** | Entries before `conflict` are not touched — log prefix invariant |
| `logWithEntries_not_in` (helper) | Low | Low | Entries not in the new suffix are looked up from the original log |
| `maybeAppend_suffix_applied` (MA14) | **High** | **Very High** | New suffix entries appear at the correct indices in the updated log |
| `logWithEntries_mem_first` (helper) | Low | Low | First entry in a non-empty suffix takes precedence |
| `maybeAppend_log_no_conflict` (MA15) | High | **High** | No conflict → log unchanged |
| `maybeAppend_state_unchanged_on_failure` (MA16) | Mid | Medium | Failed match_term → entire state unchanged |

**Assessment**: `MaybeAppend.lean` contains the richest collection of protocol-level proofs
in the FV portfolio.  MA5–MA9 fully characterise the committed-index update logic, which
is the core of Raft's safety guarantee.  MA13 (`log_prefix_preserved`) and MA14 (`suffix_applied`)
together pin down the exact semantics of the log truncation and append: the prefix before
the conflict is untouched, and the new suffix is written at the correct positions.  MA11
(`persisted_rollback`) catches a subtle class of storage-layer bugs where a write-ahead log
could be inconsistent after a truncation if the persisted boundary was not rolled back.
MA16 confirms the fail-safe property: a mismatched term causes no state mutation.

The most valuable cluster is **MA5+MA13+MA14**: these three theorems together describe
the complete semantic effect of `maybe_append` on the log and commit state.  Any
implementation that got the conflict index wrong, committed too aggressively, failed to
truncate the log, or applied entries at the wrong positions would falsify at least one of
these theorems.

---

### `Inflights.lean` — 15 theorems *(open PR — not yet merged)*

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `inflights_add_queue` (INF1) | Low | Medium | `(add x).queue = queue ++ [x]` — append semantics |
| `inflights_add_count` (INF2) | Low | Medium | Count increases by exactly 1 |
| `inflights_add_mem` (INF3) | Low | Low | Added element is in the queue |
| `inflights_count_le_cap` (INF4) | Mid | **High** | `count < cap → (add x).count ≤ cap` — flow-control safety |
| `inflights_full_iff` (INF5) | Mid | **High** | `full = true ↔ count = cap` — `full` predicate equivalence |
| `inflights_freeTo_count_le` (INF6) | Mid | Medium | `freeTo` never increases count |
| `inflights_freeTo_head_gt` (INF7) | Mid | **High** | Head of result is `> to` after `free_to` |
| `inflights_freeTo_all_gt_sorted` (INF8) | **High** | **Very High** | If sorted: all remaining entries are `> to` — Raft flow-control correctness |
| `inflights_freeTo_sorted` (INF9) | Mid | **High** | Sortedness preserved by `free_to` |
| `inflights_freeTo_noop` (INF10) | Mid | Medium | If head `> to`: `free_to` is a no-op |
| `inflights_freeFirstOne_eq_freeTo` (INF11) | Mid | Medium | `free_first_one = free_to(head)` when non-empty |
| `inflights_freeFirstOne_empty` (INF12) | Low | Low | `free_first_one` is identity on empty queue |
| `inflights_reset_queue` (INF13) | Low | Low | `reset.queue = []` |
| `inflights_reset_count` (INF14) | Low | Low | `reset.count = 0` |
| `inflights_reset_cap` (INF15) | Low | Low | `reset.cap = cap` |

**Assessment**: INF4 (`count_le_cap`) is the key safety invariant for Raft flow control:
it confirms that `add` maintains the capacity bound when called with the correct precondition
(`count < cap`).  INF8 (`freeTo_all_gt_sorted`) is the most important correctness property:
after `free_to(to)`, all remaining in-flight entries have index `> to`, confirming that
acknowledged messages are properly dequeued.  These two properties together constitute a
complete correctness specification for the `Inflights` data structure in isolation.

**Note**: This target is at phase 3 (Lean spec). Phase 4 (implementation model using the
actual ring-buffer representation) and phase 5 (stronger proofs about the ring-buffer
invariants) remain to be done.  The most valuable next step is to prove INF8 without the
sortedness hypothesis — showing that the Inflights API maintains sortedness as an invariant.

---

## Gaps and Recommendations

Prioritised by impact:

### 1. `Inflights` ring buffer — **High priority** *(phase 3 — 15 theorems proved, open PR)*

`src/tracker/inflights.rs` is the next target.  The phase-3 Lean spec (INF1–INF15) is in an
open PR.  The next steps are:

- **Phase 4** (impl model): Model the actual ring-buffer state (`start`, `buffer`, `count`)
  and prove that the abstract `queue`-based model is equivalent to the concrete ring-buffer.
  This would close the correspondence gap between the Lean model and the Rust implementation.
- **Phase 5** (stronger proofs): Prove `sortedness` as an *invariant* maintained by `add`
  (without requiring it as a hypothesis) — i.e., show that if the queue is sorted before
  `add`, it remains sorted after (this requires the `add`-at-end property, which is proved
  as INF1).  Also prove that `free_to` after a prior `add` is always well-behaved.

### 2. `progress` tracker — **High priority** *(phase 1 — unstarted)*

`src/tracker/progress.rs` manages per-peer state for the leader.  Key invariants:
`match_index ≤ next_index`, the flow-control interplay between `inflights` and `next_index`,
and the probe/replicate/snapshot state machine.  This is the next natural target after
Inflights because it uses Inflights directly.

### 3. Bridging theorem for `jointCommittedIndex` empty divergence — **Medium priority**

JCI9–JCI10 document that the Lean model returns `0` for empty configs where Rust returns
`u64::MAX`.  The practical impact: a caller that passes `outgoing = []` (non-joint config)
gets `jointCommittedIndex = min(ci_in, 0) = 0` in Lean vs `min(ci_in, MAX) = ci_in` in
Rust.  A bridging theorem showing `jointCommittedIndex incoming [] acked = committedIndex
incoming acked` does *not* hold in the current model.  Either the model should special-case
the empty-outgoing path, or a precondition `outgoing ≠ []` should be added to the joint
safety/maximality theorems.

### 4. Composition / end-to-end safety property — **Long-term goal**

No end-to-end Raft safety theorem exists yet (e.g., "two entries committed at the same
index by the same term are identical").  The building blocks now exist: quorum-safety
(CI-Safety + JCI4–JCI5), log-conflict detection (FC7+FC11), and log-append semantics
(MA5+MA13+MA14).  The next intermediate goal is a theorem connecting `maybe_append` to
`committed_index`: "if `maybe_append` returns `Some`, the new committed index is safe with
respect to the new log".  This would be the first cross-module Raft correctness theorem.

### 5. Voter-list `Nodup` precondition — **Low priority (hardening)**

Add a `voters.Nodup` hypothesis to the `_iff` theorems in `MajorityVote.lean` and
`CommittedIndex.lean`.  Currently the theorems technically hold even for duplicate voter
lists but with wrong semantics.  A `Nodup` precondition would make the model honest.

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

### Concern 4: `JointCommittedIndex` empty-config divergence

As noted above (JCI9–JCI10), the Lean model diverges from Rust when either config group
is empty.  The joint safety and maximality theorems (JCI4–JCI6) are sound for non-empty
configs but may give misleading results for configurations in transition.

---

## Positive Findings

1. **`committedIndex_safety` and `committedIndex_maximality`** are genuine discoveries:
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

5. **`maybeAppend_log_prefix_preserved`** (MA13) and **`maybeAppend_suffix_applied`**
   (MA14) together give the most complete log-correctness characterisation in the portfolio:
   the prefix is untouched and the suffix is correctly applied.  These two theorems together
   with MA5 (`committed_eq`) constitute a complete post-condition for `maybe_append`.

6. **`inflights_freeTo_all_gt_sorted`** (INF8) confirms the Raft flow-control correctness
   property: after acknowledging up to index `to`, all remaining in-flight entries are
   strictly newer.  This directly validates the Inflights data structure's role in the
   Raft pipelining protocol.

7. **No bugs found** in any of the nine verified functions.  This is evidence (not proof)
   that the Raft quorum logic, log operations, config validation, and flow control as
   implemented are correct for the modelled paths.

---

> 🔬 Generated by [Lean Squad](https://github.com/dsyme/fv-squad/actions/runs/23714161005) automated formal verification.
