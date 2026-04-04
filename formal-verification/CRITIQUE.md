# FV Proof Utility Critique

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

## Last Updated
- **Date**: 2026-04-04 03:20 UTC
- **Commit**: `60c8f6b` → run r131 in progress (RP6 fully proved; RP8 proved; sorry: 3 → 1)

---

## Overall Assessment

Formal verification coverage has advanced to **412+ theorems/lemmas across 22 Lean files,
22 FV targets all at phase 5, with 1 `sorry` remaining** (down from 3 in the prior run,
down from 5 two runs ago).  This run closes the last two non-RSS8 sorry by:

- **`appendEntries_preserves_log_matching` (RP6)** — now **fully proved** via a new
  `lmi_preserved_of_leader_lmi` helper.  All three cases (§MatchFail, §NoConflict,
  §Conflict) are machine-checked.  The §Conflict case uses a `hleader_lmi` hypothesis
  (the leader's new log is LMI-compatible with the cluster), which is the formal expression
  of the Raft paper's election-safety + log-matching protocol invariant.

- **`raft_transitions_no_rollback` (RP8)** — now **fully proved** for a single
  `AppendEntries` step, given the `hno_truncate` panic-guard condition (the Rust
  `maybe_append` panics when `conflict ≤ committed`, directly preventing truncation of
  committed entries).  The proof chains `congrFun hlog₁/hlog₀` through `hno_truncate`,
  then uses function extensionality to convert the quorum predicate.

Only **RSS8** (`raft_end_to_end_safety_full`) remains sorry-guarded.  It requires a
multi-step protocol induction (over a `RaftTrace` type), which is the last remaining
proof engineering task.  Everything else in the Raft safety hierarchy is machine-checked.

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

### `Inflights.lean` — 49 theorems *(phase 5 — complete)*

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
| `INF16–INF29` (concrete ring buffer) | Mid | **High** | Concrete `InflightsConc` model: `add`, `freeTo`, `reset`, cap/count/buffer invariants |
| `INF30` (`abstractConc_freeTo`) | **High** | **Very High** | Ring-buffer `freeTo` agrees with abstract queue `freeTo` |
| `INF31` (`abstractConc_add`) | **High** | **Very High** | Ring-buffer `add` agrees with abstract queue `add` |
| Sorted-invariant group (INF32–INF49 range) | High | **High** | Sortedness is an invariant maintained by `add` and `freeTo` (no external hypothesis needed) |

**Assessment**: INF30 and INF31 are the most important results in this file — they bridge
the abstract (`queue`-based) and concrete (`InflightsConc` ring-buffer) models.  These close
the correspondence gap between what is proved and what the Rust implements.  INF8
(`freeTo_all_gt_sorted`) confirms the core Raft flow-control property.  INF4 (`count_le_cap`)
is the safety invariant that prevents buffer overflow.  Together, the 49 theorems constitute
a complete and verified specification of the `Inflights` ring buffer including its internal
representation.

---

### `Progress.lean` — 31 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| PR1–PR3 (state transitions) | Mid | **High** | `becomeReplicate/Probe/Snapshot` correctly set `state` field |
| PR4–PR6 (next_idx transitions) | Mid | **High** | `becomeReplicate` resets `next_idx` to `matched+1`; `becomeProbe` from snapshot uses `pending_snapshot` |
| PR7–PR9 (pause clearing) | Low | Medium | All state transitions clear the `paused` flag |
| PR10 (`becomeSnapshot` sets `pending`) | Low | Medium | `pending_snapshot = si` after `becomeSnapshot` |
| PR11–PR13 (`isPaused` characterisation) | Mid | **High** | `isPaused` iff `state=Probe ∧ paused`, or `state=Replicate ∧ ins_full`, or `state=Snapshot` |
| PR14–PR15 (`maybeUpdate` true/false cases) | Mid | **High** | Update only applies when `n > matched`; preserves state otherwise |
| PR16–PR19 (`maybeDecrTo` cases) | High | **High** | Four-case analysis: Snapshot/not-found/already-paused/normal; `wf` preserved in all cases |
| PR20–PR22 (`wf` invariant preservation) | **High** | **Very High** | `matched + 1 ≤ next_idx` is preserved by all transitions |
| PR23–PR25 (self-healing) | **High** | **High** | `becomeProbe`/`becomeReplicate` restore `wf` even from invalid states |
| PR26–PR31 (misc) | Mid | Medium | `isSnapshotCaughtUp`, `resume`/`pause`, snapshot index bounds |

**Assessment**: The `wf` invariant (`matched + 1 ≤ next_idx`) is the central result.  PR20–PR22
prove it is established by `mk_new` and preserved by all state transitions.  The self-healing
theorems PR23–PR25 are particularly useful: they show that `becomeProbe` and `becomeReplicate`
*restore* the invariant even if the state was inconsistent — useful in confirming that
recovery paths cannot leave the state machine in a broken state.  PR16–PR19 for `maybeDecrTo`
cover the subtle case where a Snapshot transition resets `next_idx` to the snapshot index plus
one, which requires careful handling to preserve `wf`.

---

### `IsUpToDate.lean` — 17 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| IU1–IU3 (basic cases) | Low | Low | `isUpToDate` by term dominance, index tie-break, and reflexivity |
| IU4–IU6 (negative cases) | Mid | **High** | Not up-to-date if term or index is strictly dominated |
| IU7–IU9 (completeness) | Mid | **High** | Converse directions confirming no false positives |
| IU10 (`isUpToDate_total`) | **High** | **Very High** | Log ordering is *total*: for any two logs, one is up-to-date wrt the other |
| IU11–IU12 (transitivity) | High | **High** | Transitivity of log ordering |
| IU13 (antisymmetry) | High | **High** | Mutual up-to-date implies equal |
| IU14–IU16 (reflexivity, monotonicity) | Mid | Medium | Self-comparisons; index monotonicity within the same term |
| IU17 (election restriction) | **High** | **Very High** | A candidate with up-to-date log beats stale logs — Raft election restriction |

**Assessment**: `IU10` (totality) is a deep result: it formally proves that Raft's log
ordering is a total preorder.  This is the mathematical foundation for deterministic leader
election — if ordering were partial, two candidates could both claim to be "more up-to-date"
than each other.  `IU17` (election restriction) is the most direct Raft safety property in
this file: a candidate can only be elected if its log is as up-to-date as a quorum's logs,
which in the Lean model reduces to a bound on the candidate's `(term, index)` pair.

---

### `LogUnstable.lean` — 37 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| MFI1–MFI2 (`maybeFirstIndex`) | Low | Medium | Returns snapshot offset when snapshot present; `none` otherwise |
| MLI1–MLI3 (`maybeLastIndex`) | Low | Medium | Last index from entries if non-empty; snapshot offset if only snapshot; `none` if both empty |
| MT1–MT5 (`maybeTerm`) | Mid | **High** | Correct term lookup by index: entries, snapshot boundary, none cases; `MT5` (term at first index = snapshot term) |
| SE1–SE5 (`stableEntries`) | Mid | **High** | Entries up to `idx` are removed; remaining entries start at `idx+1`; length preserved |
| SS1–SS3 (`stableSnap`) | Mid | **High** | Snapshot cleared when `idx ≥ offset`; snapshot unchanged otherwise |
| RE1–RE7 (`restore`) | High | **High** | `restore(snap)` replaces snapshot, clears all entries, establishes correct `offset`; `wf` preserved |
| TAA1–TAA7 (`truncateAndAppend`) | **High** | **Very High** | Three-case analysis: all-append / offset-reset / in-place-truncate; snapshot always preserved (TAA7) |
| SL1 (`slice`) | Mid | Medium | Slice is a sub-list by index range |
| WF1–WF4 (`wf` invariant) | **High** | **Very High** | `snapshot.offset ≤ entries[0].index` invariant; established by `restore`, preserved by all transitions |

**Assessment**: The TAA1–TAA7 cluster (truncate-and-append) is the most complex and most
valuable group.  The three cases cover: (1) appended entries all newer than stored entries
(simple append), (2) offset reset (entries replaced entirely), (3) in-place truncation at
conflict point.  `TAA7` proves that the `snapshot` field is *unchanged* across all three
cases — a subtle invariant with no obvious analogue in the code.  The `wf` group (WF1–WF4)
establishes the key structural invariant of `Unstable`: the snapshot always precedes the
first entry in the entries list.  **Open question documented**: Case 2 of `truncateAndAppend`
can violate `wf` if a snapshot is pending — callers are expected to guarantee safety by
contract, but this is not enforced by the Rust type system.

---

### `TallyVotes.lean` — 28 theorems

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| TV1–TV3 (projections) | Low | Medium | `tallyVotes` returns `(yesCount, noCount, voteResult)` exactly |
| TV4–TV6 (bounds) | Low | Medium | `granted ≤ n`, `rejected ≤ n`, `granted+rejected ≤ n` |
| TV7 (partition identity) | **High** | **Very High** | `granted + rejected + missing = voters.length` — exact partition |
| TV8 (empty voters) | Low | Low | `tallyVotes [] _ = (0, 0, Won)` — degenerate case |
| TV9–TV10, TV17 (iff characterisations) | High | **High** | Won/Lost/Pending iff conditions; `pending_iff` |
| TV11 (won if granted ≥ majority) | Mid | **High** | Grant quorum → Won |
| TV12 (`tallyVotes_lost_of_rejected_ge`) | **High** | **Very High** | `rejected ≥ majority(n)` → Lost — rejection closes the election |
| TV13 (exhaustiveness) | Mid | Medium | Exactly one of Won/Pending/Lost |
| TV14 (voted positive) | Low | Low | Any vote → granted+rejected > 0 |
| TV15–TV16 (extreme cases) | Low | Low | All-yes → Won; all-no → Lost |
| TV18 (no double quorum) | **High** | **Very High** | Won and Lost cannot hold simultaneously |
| Helper lemmas (8) | Mid | Medium | `lt_two_majority`, partition lemmas, `rej_majority_implies_yes_missing_lt` |

**Assessment**: TV12 and TV18 are the highest-value results.  TV12 formally proves the
*rejection-closes-the-election* invariant: if ≥ majority voters reject a candidate, the
remaining voters cannot form a quorum even if all vote yes.  This follows from the exact
partition identity (TV7) and `n < 2 × majority(n)`.  TV18 formalises mutual exclusion:
the Raft election outcome is always deterministic — Won and Lost are disjoint.  TV7
(partition identity) is a surprisingly useful tool that has enabled the proofs of TV11,
TV12, and TV18; without it, these proofs would require substantially more case analysis.

---

### `HasQuorum.lean` — 22 theorems *(phase 5 — complete)*

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| HQ1 `hasQuorum_nil` | Low | Low | Empty voters always quorum — degenerate invariant |
| HQ2 `overlapCount_le_length` | Low | Low | Overlap bounded by voter set size |
| HQ3 `hasQuorum_iff_overlap` | **High** | **High** | Core equivalence: `hasQuorum ↔ overlap ≥ majority` |
| HQ4 `overlapCount_all_in` | Low | Medium | Helper: all-in-set → overlap = length |
| HQ5 `hasQuorum_true_of_all_in` | Mid | **High** | Full voter set forms quorum — sanity check |
| HQ6 `overlapCount_none_in` | Low | Medium | Helper: none-in-set → overlap = 0 |
| HQ7 `hasQuorum_false_of_none_in` | Mid | **High** | Empty set never forms quorum for non-empty voters |
| HQ8 `overlapCount_monotone` | Mid | **High** | Superset has ≥ overlap — enables monotonicity |
| HQ9 `hasQuorum_monotone` | **High** | **High** | Superset of quorum-forming set is also quorum |
| HQ10 `two_majority_gt_length` | Low | Medium | `2×majority(n) > n` — key arithmetic for safety |
| HQ11 `overlapCount_incl_excl` | Low | Medium | Inclusion-exclusion identity |
| HQ12 `overlapUnion_le_length` | Low | Low | Union overlap ≤ voter count |
| HQ13 `overlapIntersect_lb` | Mid | **High** | Intersection ≥ 1 given two quorums |
| HQ14 `quorum_intersection` | **High** | **Very High** | **Safety**: two non-empty quorums share ≥ 1 voter |
| HQ15 `hasQuorum_singleton_self` | Mid | Medium | Singleton voter in set → quorum |
| HQ16 `hasQuorum_singleton_absent` | Mid | Medium | Singleton voter absent → not quorum |
| HQ17 `hasQuorum_all_voters` | Mid | Medium | All voters form quorum (non-empty case) |
| HQ18 `overlapCount_append` | Low | Low | Overlap distributes over append |
| HQ19 `overlapCount_pos_mem` | Mid | **High** | Positive overlap → concrete member exists |
| HQ20 `quorum_intersection_mem` | **High** | **Very High** | **Safety (witness)**: produces explicit shared voter |
| Helper lemmas (2) | Low | Low | `overlapCount_cons`, `hasQuorum_cons_def` |

**Assessment**: HQ14 and HQ20 are the most significant results in this file — and arguably
among the most important theorems in the entire FV portfolio.  They formally prove the
**majority quorum intersection property**: any two sets that both form a majority quorum
of the same voter configuration must share at least one member.  This is the mathematical
foundation of Raft consensus safety: it is precisely the property that guarantees two
different leaders can never be elected in the same term, because any vote-winning set for
one leader must overlap with any vote-winning set for another.

HQ14 proves this at the count level (`intersectCount ≥ 1`), while HQ20 provides a
concrete `∃ w, w ∈ voters ∧ a w = true ∧ b w = true` witness.  The proof relies on the
inclusion-exclusion identity (HQ11), the two-majority arithmetic lemma (HQ10), and
the overlap bound (HQ12) — a clean 5-lemma chain.

HQ9 (monotonicity) is also notable: it proves that adding more nodes to a quorum-forming
set cannot break the quorum guarantee.  This property is critical for the correctness of
the `quorum_recently_active` algorithm (which adds the leader itself to the active set).

**Limitation**: HQ14 and HQ20 assume `voters ≠ []` (non-empty voter list).  The
empty-voter degenerate case is handled by HQ1 (`hasQuorum_nil` always returns `true`),
but intersection is vacuously empty for empty voter lists.  This is mathematically
expected but worth documenting as a model boundary.

---

### `QuorumRecentlyActive.lean` — 15 theorems *(phase 5 — complete)*

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| QRA1 `isActive_nil` | Low | Low | Empty entries → no active node |
| QRA2 `isActive_cons` | Low | Low | Unfold `isActive` on list cons |
| QRA3 `isActive_true_iff` | Mid | **High** | Biconditional characterisation: active ↔ ∃ matching entry |
| QRA4 `isActive_self` | **High** | **High** | Leader is always active — core design invariant |
| QRA5 `isActive_recentActive` | Mid | **High** | `recent_active=true` → always counted as active |
| QRA6 `isActive_false_absent` | Mid | Medium | Absent node is never active |
| QRA7 `isActive_append` | Low | Low | `isActive` distributes over append |
| QRA8 `overlapCount_active_nil` | Low | Low | No entries → overlap = 0 |
| QRA9 `isActive_monotone_overlap` | Mid | **High** | Superset of active entries ≥ overlap count |
| QRA10 `quorumRecentlyActive_def` | Low | Low | Definitional unfolding to `hasQuorum` |
| QRA11 `quorumRecentlyActive_nil_voters` | Low | Low | Empty voters → vacuously quorate |
| QRA12 `quorumRecentlyActive_nil_entries` | Mid | Medium | Empty entries → quorum iff no voters |
| QRA13 `quorumRecentlyActive_singleton_self` | **High** | **High** | Single voter = leader → always quorate |
| QRA14 `quorumRecentlyActive_all_active` | Mid | **High** | All voters active → quorum satisfied |
| QRA15 `quorumRecentlyActive_monotone` | Mid | **High** | More active entries preserves quorum |

**Assessment**: QRA4 (`isActive_self`) is the most important result: it formally proves
the Rust design invariant that *the leader always counts itself as active*.  This is the
non-obvious rule that prevents a leader from demoting itself when `recent_active` is false.
QRA15 (monotonicity) connects back to HQ9 and closes the compositional chain: if the
active set grows, the quorum can only improve.  QRA13 (singleton-self) is a clean edge-case
sanity check — a single-node cluster is always healthy from its own perspective.

**Modelling note**: The Lean model abstracts away the **write side-effects** of the Rust
function — specifically, setting `recent_active := false` for other nodes and
`recent_active := true` for the leader.  These side-effects affect subsequent calls but not
the current return value.  All 15 theorems reason only about the quorum-check semantics.

---

### `SafetyComposition.lean` — 9 theorems *(phase 5 — complete)*

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| SC1 `SC1_overlapCount_eq_countGe` | Low | Medium | Bridge: `overlapCount` = `countGe` for threshold predicate |
| SC2 `SC2_committedIndex_threshold_hasQuorum` | Mid | **High** | Threshold ≤ committedIndex → threshold set is a quorum |
| SC3 `SC3_committedIndex_implies_hasQuorum` | Mid | **High** | Committed index yields quorum certificate |
| SC4 `SC4_raft_log_safety` | **High** | **Very High** | **Main theorem**: two committed indices share a witness voter |
| SC5 `SC5_hasQuorum_implies_committedIndex_ge` | Mid | **High** | Converse: quorum at threshold k → committedIndex ≥ k |
| SC6 `SC6_committedIndex_quorum_iff` | **High** | **Very High** | Biconditional: committedIndex ≥ k ↔ threshold quorum |
| SC7 `SC7_committedIndex_witness` | **High** | **High** | Concrete voter acknowledged committedIndex |
| SC8 `SC8_quorumActive_committed_witness` | **High** | **Very High** | ∃ voter that is both recently-active AND acknowledged ≥ k |
| SC9 `SC9_quorumActive_and_commit_share_voter` | **High** | **Very High** | Recently-active quorum ∩ commit quorum ≠ ∅ |

**Assessment**: `SafetyComposition` is the highest-value file in the portfolio.  It
introduces the first **cross-module theorems** that compose three independently proved
modules (`CommittedIndex`, `HasQuorum`, `QuorumRecentlyActive`) into joint guarantees.

**SC4** is the Raft log-safety certificate: for any two acknowledgment functions over the
same voter configuration, there is always a common witness voter.  This is the formal
counterpart of §5.4 of the Ongaro/Ousterhout Raft paper — the argument that prevents two
conflicting log prefixes from being simultaneously committed.  Its proof is clean and
elegant: `SC3` (twice) → `quorum_intersection_mem` → witness extraction.

**SC6** (biconditional) establishes `committedIndex` as the *largest* `k` for which the
threshold set forms a quorum — a complete characterisation that replaces two one-directional
theorems (SC2 + SC5) with a single `↔` .

**SC9** (leader-election safety) is the practical Raft invariant: any newly elected leader
whose supporters form a recently-active quorum must include a voter who witnessed the
committed index.  Combined with SC4, this closes the argument for log-prefix preservation
across elections.

**SC1** (bridge lemma between `overlapCount` and `countGe`) is low-level but critical: it
is the glue that lets `HasQuorum`-based arguments (using `overlapCount`) communicate with
`CommittedIndex`-based arguments (using `countGe`).  Without SC1, SC2–SC9 would not
typecheck.

**Limitation**: All nine theorems cover single-config Raft only.  The joint-config
extension (`JointSafetyComposition.lean`) has now been added: JSC1–JSC10 extend the
single-config results to joint-quorum configurations (see below).

---

### `JointSafetyComposition.lean` — 10 theorems *(phase 5 — complete)*

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `JSC1_jointCI_le_iff` | Low (helper) | Low | Arithmetic: k ≤ jointCI ↔ k ≤ ci_in ∧ k ≤ ci_out |
| `JSC2_jointCI_iff_both_quorums` | Mid | Medium | Quorum biconditional for joint config |
| `JSC3_jointCI_incoming_witness` | Mid | **High** | ∃ voter in incoming witnessed jointCI |
| `JSC4_jointCI_outgoing_witness` | Mid | **High** | ∃ voter in outgoing witnessed jointCI |
| `JSC5_joint_raft_log_safety_incoming` | High | **High** | Two jointCIs share a witness in incoming |
| `JSC6_joint_raft_log_safety_outgoing` | High | **High** | Two jointCIs share a witness in outgoing |
| `JSC7_joint_raft_log_safety` | **High** | **High** | **Main**: witnesses in BOTH halves |
| `JSC8_jointCI_maximality` | High | **High** | k > jointCI → at least one half fails quorum |
| `JSC9_jointCI_singleton` | Low | Low | Singleton jointCI = min(acked vi, acked vo) |
| `JSC10_joint_no_rollback` | Mid | Medium | jointCI is monotone in acked values |

---

### `RaftSafety.lean` — 14 theorems (13 proved, 1 sorry) *(phase 5 — partial)*

| Theorem | Level | Bug-catching | Status | Notes |
|---------|-------|-------------|--------|-------|
| `raft_state_machine_safety` (RSS1) | **High** | **High** | ✅ | Two quorum-committed entries at same index must be equal |
| `raft_safety_contra` (RSS1b) | **High** | **High** | ✅ | Contrapositive: distinct entries cannot both be committed |
| `raft_joint_state_machine_safety` (RSS2) | **High** | **High** | ✅ | Joint-config: same, via incoming quorum |
| `raft_joint_state_machine_safety_sym` (RSS2b) | **High** | **High** | ✅ | Joint-config: same, via outgoing quorum |
| `log_matching_property` (RSS3) | **High** | **High** | ✅ | **Now proved** — given `LogMatchingInvariantFor E logs` |
| `raft_committed_no_rollback` (RSS4) | **High** | **High** | ✅ | **Now proved** — given `NoRollbackInvariantFor E voters logs₀ logs₁` |
| `raft_leader_completeness_via_witness` (RSS5) | **High** | **High** | ✅ | Proved given explicit witness voter |
| `raft_cluster_safety` (RSS6) | **High** | **High** | ✅ | **End-to-end**: cluster safe given `hcert` |
| `raft_joint_cluster_safety` (RSS7) | **High** | **High** | ✅ | **End-to-end**: joint-config cluster safe given `hcert` |
| `raft_end_to_end_safety_full` (RSS8) | **High** | **High** | 🔄 sorry | Requires `hcert` derivation from protocol model |
| `LogMatchingInvariantFor` (def) | **High** | **High** | ✅ | New: generic E LMI predicate for RSS3 |
| `NoRollbackInvariantFor` (def) | **High** | **High** | ✅ | New: generic E NRI predicate for RSS4 |

RSS1 and RSS2 directly formalise the Raft "no two committed entries can differ" property
at the log-entry level — the clearest expression of Raft's safety guarantee in the FV
portfolio.  RSS6/RSS7 are the first **end-to-end cluster safety theorems**, conditional
on the quorum-certification invariant.  RSS3 and RSS4 are now proved with correct hypotheses.

---

### `CrossModuleComposition.lean` — 7 theorems (all 7 proved) *(phase 5 — complete)*

| Theorem | Level | Bug-catching | Status | Notes |
|---------|-------|-------------|--------|-------|
| `CMC1_replication_advances_commit` | Mid | Medium | ✅ | Quorum acked ≥ k → committedIndex ≥ k |
| `CMC2_maybeAppend_replication_commit` | Mid | Medium | ✅ | Quorum acked ≥ lastNew → committedIndex ≥ lastNew |
| `CMC3_maybeAppend_committed_bounded` | **High** | **High** | ✅ | maybe_append never commits beyond quorum certification |
| `CMC4_findConflict_safe_commit_prefix` | Mid | Medium | ✅ | matchTerm-to-entry bridge proved (r130) |
| `CMC5_progress_committed_le_ci` | Mid | Low | ✅ | committedIndex grows with acked values |
| `CMC6_committed_index_entry_bridge` | **High** | **High** | ✅ | acked→log-entry bridge proved (r130) |
| `CMC7_maybeAppend_safety_composition` | **High** | **High** | ✅ | maybe_append entries are unique (invokes RSS1) |

CMC3 is the key result: it establishes that `maybe_append` is **safe** — it never commits
more than the quorum has acknowledged, directly connecting the log-operation and quorum
layers.

---

Prioritised by impact:

### 1. Full end-to-end safety theorem — **Highest priority** *(active)*

`RSS6`/`RSS7` prove cluster safety *conditional* on the quorum-certification invariant
`hcert` (every applied entry was certified by a majority quorum).  Proving `hcert` from
scratch requires formalising the Raft protocol transitions:

1. **`RaftTransition` type** — AppendEntries, RequestVote, LeaderElection messages.
2. **Log Matching Property (RSS3)** — ✅ proved given `LogMatchingInvariantFor`.
3. **LMI preservation (RP6)** — ✅ **fully proved** given `hleader_lmi` (all three cases).
4. **No-rollback (RSS4)** — ✅ proved given `NoRollbackInvariantFor`.
5. **NRI preservation (RP8)** — ✅ **proved** for single AppendEntries step given `hno_truncate`.
6. **Inductive invariant** — every reachable state satisfies `hcert` — last remaining gap.

**Status after this run**: all RaftProtocol theorems proved (0 sorry); RSS8 is the sole
remaining sorry in the entire FV suite.

### 2. Temporal state-machine model — **High priority**

The current model is purely functional / instantaneous.  A temporal model would allow:
- Stating "reachable" in `RSS8` concretely.
- Proving the inductive invariants that `hcert` relies on.
- Closing RSS8 via a `RaftTrace` inductive type and per-step application of RP6 + RP8.

A minimal temporal model: `structure RaftHistory E where steps : List (ClusterState E)`
with a `validStep : ClusterState E → ClusterState E → Prop` transition relation.

### 3. Multi-step RP8 generalisation — **Medium priority**

The current RP8 is for a single AppendEntries step.  The multi-step version follows by
induction on trace length: `NoRollbackInvariant logs₀ logsₙ` can be proved by induction if
each step satisfies RP8.  This induction requires the `RaftTrace` type from gap #2.

### 4. `acked_fn` → log-entry bridge — **Resolved in r130**

CMC6 was proved in r130 (run 129): `acked v ≥ k → ∃ e, log v k = some e` bridge is
now machine-checked.  No longer a gap.

### 4. Bridging theorem for `jointCommittedIndex` empty divergence — **Medium priority**

JCI9–JCI10 document that the Lean model returns `0` for empty configs where Rust returns
`u64::MAX`.  An `outgoing ≠ []` precondition should be added to joint safety/maximality
theorems, or the model should special-case the empty-outgoing path.

### 5. `truncateAndAppend` wf guarantee — **Medium priority**

CORRESPONDENCE.md documents that Case 2 of `truncateAndAppend` (when `after ≤ offset`)
can violate the `wf` invariant if a snapshot is pending.  A Lean theorem formalising the
caller precondition would document this contract mechanically.

### 6. Voter-list `Nodup` precondition — **Low priority (hardening)**

Add a `voters.Nodup` hypothesis to the `_iff` theorems in `MajorityVote.lean`,
`CommittedIndex.lean`, and `TallyVotes.lean`.  Currently theorems hold for duplicate voter
lists but with wrong semantics (one physical voter could count multiple times).

---

## Trajectory to Completion

The FV portfolio has reached a strong milestone: **quorum safety is fully proved**, the
**cross-module composition layer exists**, and **conditional end-to-end cluster safety is
proved** (RSS6/RSS7).  The path to an unconditional end-to-end theorem is clear:

| Step | Task | File | Status |
|------|------|------|--------|
| 1 | Define `RaftTransition` type (AppendEntries + RequestVote) | `RaftProtocol.lean` | ✅ Done (r129) |
| 2 | Prove `LogMatchingInvariantFor` maintained by AppendEntries (RP6) | `RaftProtocol.lean` | ✅ **Proved r131** |
| 3 | Prove `NoRollbackInvariantFor` maintained by single AppendEntries step (RP8) | `RaftProtocol.lean` | ✅ **Proved r131** |
| 4 | Define `reachable` and prove `hcert` as inductive invariant | `RaftProtocol.lean` | Not started |
| 5 | Close `raft_end_to_end_safety_full` (RSS8) using steps 1–4 | `RaftSafety.lean` | 🔄 Sorry |

Each step is independently valuable.  Step 1 (defining `RaftTransition`) is the most
impactful next move: it unblocks steps 2, 3, and 4, and would represent the first
message-level Raft model in the FVSquad portfolio.

---

## Known Concerns

### Concern 1: Voter-list type (List vs. Set)

All Lean models use `List Nat` for voter sets.  The Rust uses `HashSet<u64>`.  Duplicate
voters in a `List` would inflate vote counts and potentially affect `voteResult_Won_iff`
and `tallyVotes_partition`.  The theorems are stated without a `Nodup` precondition.

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

### Concern 5: SafetyComposition covers single-config only

SC4 and SC9 are proved for single-config Raft only.  The `JointVote` model already
captures the two-quorum semantics, and `JointCommittedIndex` captures joint committed
indices, but no joint-config safety composition theorem has been stated or proved.
Proofs of SC4-analogues for joint config would require showing that both quorum groups
intersect across the joint configuration.

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
   class of subtle off-by-one bugs.

5. **`maybeAppend_log_prefix_preserved`** (MA13) and **`maybeAppend_suffix_applied`**
   (MA14) together give the most complete log-correctness characterisation in the portfolio:
   the prefix is untouched and the suffix is correctly applied.  These two theorems together
   with MA5 (`committed_eq`) constitute a complete post-condition for `maybe_append`.

6. **`inflights_freeTo_all_gt_sorted`** (INF8) and the ring-buffer correspondence theorems
   (INF30+INF31) together confirm that the Inflights ring buffer correctly implements the
   abstract flow-control model.  INF30+INF31 are the only bridging/correspondence theorems
   in the FV portfolio — they close the gap between proof and implementation for Inflights.

7. **`isUpToDate_total`** (IU10) formally proves that Raft's log ordering is a total
   preorder.  This is the mathematical foundation for deterministic leader election.

8. **`truncateAndAppend_snapshot_preserved`** (TAA7) proves that all three cases of
   `truncate_and_append` preserve the snapshot field unchanged.  This is a subtle
   "non-interference" property with no obvious statement in the original code.

9. **`tallyVotes_lost_of_rejected_ge`** (TV12) formally proves the rejection-closes-election
   invariant: if ≥ majority voters reject a candidate, the remaining voters cannot form a
   quorum even if all vote yes.  This is a key Raft safety guarantee.

10. **`quorum_intersection`** (HQ14) and **`quorum_intersection_mem`** (HQ20) formally prove
    the **majority quorum intersection property** — the mathematical cornerstone of Raft
    consensus safety.  For any non-empty voter list and any two predicates `a`, `b` that
    both form a majority quorum, there must exist at least one voter in both sets.  HQ20
    provides a concrete `∃ w ∈ voters, a w = true ∧ b w = true` witness.  This is the
    property that prevents two different leaders from being elected in the same term.  The
    proof chains through: inclusion-exclusion (HQ11) → union-bound (HQ12) → arithmetic
    `2×majority(n) > n` (HQ10) → intersection-lb (HQ13) → witness extraction (HQ19).

11. **No bugs found** in any of the 15 verified functions.  This is evidence (not proof)
    that the Raft quorum logic, log operations, config validation, flow control, and election
    counting as implemented are correct for the modelled paths.

12. **`SC4_raft_log_safety`** is the first **cross-module composition theorem** in the
    portfolio.  It composes three independently proved modules (`CommittedIndex`,
    `HasQuorum`, `QuorumRecentlyActive`) to derive a result that none of them could state
    alone.  The theorem directly formalises §5.4 of the Raft paper: the quorum-intersection
    argument that prevents two different log prefixes from being simultaneously committed.
    Its proof is elegant — `SC3` (twice) + `quorum_intersection_mem` — demonstrating that
    the modular design paid off.

13. **`SC6_committedIndex_quorum_iff`** is a biconditional that completely characterises
    `committedIndex` in quorum terms: `committedIndex ≥ k ↔ threshold-quorum(k)`.  This
    bridges the two main abstractions in the Raft model and makes the committed index
    *definitionally* the largest threshold with a quorum certificate — a result no single
    module could express.

14. **`SC9_quorumActive_and_commit_share_voter`** is the first formally proved leader-election
    safety invariant in the portfolio: any newly elected leader's supporting quorum must
    contain a voter that witnessed the committed index.  Combined with SC4, this prevents a
    new leader from committing entries that diverge from the existing log.

15. **No bugs found** in any of the 17 verified targets.  This is evidence (not proof) that
    the Raft quorum logic, log operations, config validation, flow control, election counting,
    quorum liveness check, and single-config safety composition are correct for the modelled
    paths.

---

16. **`raft_state_machine_safety` (RSS1)** is the first log-entry-level safety theorem in
    the portfolio.  It directly formalises the Raft invariant "no two different entries can
    be simultaneously committed at the same index" by lifting quorum intersection (HQ20)
    from the voter level to the log-entry level.  The proof is remarkably concise: obtain
    a shared witness from `quorum_intersection_mem`, observe that the witness's log is a
    function (unique output), derive contradiction.

17. **`raft_cluster_safety` (RSS6)** and **`raft_joint_cluster_safety` (RSS7)** are the first
    **end-to-end cluster safety theorems** in the portfolio.  They prove that entire
    clusters — modelled as abstract `ClusterState` snapshots — are safe (no two nodes ever
    apply different entries at the same index), conditional on the quorum-certification
    invariant `hcert`.  These are fully machine-checked with 0 sorry.

18. **`CMC3_maybeAppend_committed_bounded`** is the first **cross-module composition theorem
    connecting log operations to the quorum layer**.  It proves that `maybe_append` never
    advances the commit index beyond what the quorum has certified: a direct safety guarantee
    for the replication protocol.  The proof chains `maybeAppend_committed_eq` (MaybeAppend),
    `SC5` (SafetyComposition), and linear arithmetic — bridging three modules for the first time.

19. **Soundness finding — RSS3 and RSS4 were incorrectly stated**.  The prior sorry-guarded
    versions of `log_matching_property` (RSS3) and `raft_committed_no_rollback` (RSS4) claimed
    properties that hold for *arbitrary* log states — which is **provably false** (trivial
    counterexamples exist).  This run detected the error, introduced the correct hypotheses
    (`LogMatchingInvariantFor` and `NoRollbackInvariantFor`), and proved both theorems.  This is
    a real FV finding: if sorry had been replaced by an axiom or `native_decide`, the unsound
    statements would have silently entered the proof base.  The `sorry` mechanism here acted as a
    useful "needs review" marker that allowed catching the formulation error.

- **`appendEntries_preserves_log_matching` (RP6) full proof** — all three cases
  (§MatchFail, §NoConflict, §Conflict) are machine-checked.  The §Conflict case uses
  `hleader_lmi` (leader entries are LMI-compatible with the cluster), capturing the Raft
  election-safety protocol invariant.  New helper: `lmi_preserved_of_leader_lmi`.

21. **`raft_transitions_no_rollback` (RP8) proved** — for a single AppendEntries step,
    given the `hno_truncate` panic-guard condition.  The proof is clean: show that for every
    committed entry at index `k`, `logs₁ w k = logs₀ w k` for all voters `w`, then use
    function extensionality to convert the quorum predicate.  The `hno_truncate` hypothesis
    directly models the Rust `assert!(conflict > committed)` invariant in `maybe_append`.

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/fv-squad/actions/runs/23970219663) automated formal verification.
