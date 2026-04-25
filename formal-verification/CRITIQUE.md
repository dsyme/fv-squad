# FV Proof Utility Critique

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

## Last Updated
- **Date**: 2026-04-25 04:00 UTC
- **Commit**: `09ddbe5` — Run 105: Task 7 (Critique update — 628T, 65 files, 0 sorry); PT22–PT24 membership theorems added

---

## Overall Assessment

The FV project has produced **628 theorem declarations across 65 Lean files, machine-checked by
Lean 4 (version 4.30.0-rc2, stdlib only — no Mathlib), with 0 `sorry`**.

Since the last critique (Run 76, 50 files, 569T), the project has expanded significantly across
**five new proof layers** and **a deeper correspondence test suite**:

- **Layer 10: Election Model** — `RaftElection.lean` (53 theorems, RE1–RE53): complete election
  safety (`electionSafety` RE5), full `voteGranted` biconditionals (RV1–RV8), and a model of the
  concrete vote-granting logic from `src/raft.rs`.

- **Layer 11: Joint Membership Change Safety** — `JointTally.lean` (14T, JT1–JT9) and
  `JointSafetyComposition.lean` (10T, JSC1–JSC10) formalise the joint-quorum outcome and prove
  the joint committed index satisfies both incoming and outgoing safety simultaneously.  Together
  with `JointCommittedIndex.lean` (10T, JCI1–JCI10), this gives an end-to-end safety certificate
  for Raft membership changes.

- **Layer 12: Multi-step Safety** — `MultiStepReachability.lean` (7T, MS1–MS7) closes the
  N-step gap: `listStep_safe` (MS2) is a complete end-to-end safety certificate for an arbitrary
  finite sequence of well-formed AppendEntries steps.

- **Layer 13: Progress Tracker** — `ProgressTracker.lean` (24T, PT1–PT24): the per-peer wf
  invariant is preserved by all six operations (`removePeer`, `insertPeer`, `updatePeer`,
  `applyChange`, `applyChanges`, `initTracker`), plus membership (key-presence) theorems
  PT16–PT24 including the new `initTracker`-membership biconditional (PT22–PT23) and
  `applyChanges` stability for unaffected peers (PT24).

- **Layer 14: Configuration Invariants** — `ConfigurationInvariants.lean` (11T, CI1–CI12):
  `VotersLearnersDisjoint` formalised and proved for `mkConfiguration`; CI9–CI12 formalise a
  **key finding**: the strict 4-clause disjointness predicate is *stricter* than the Rust
  demotion state, which allows `outgoing ∩ learners_next ≠ ∅`.  A relaxed 3-clause predicate
  (`VotersLearnersDisjointRelaxed`) is proved to match the actual Rust semantics.

- **Layer 15: ReadOnly** — `ReadOnly.lean` (13T, RO1–RO13): ReadIndex linearisability
  bookkeeping (`addRequest`, `recvAck`, `advance`) fully specified and proved; 0 sorry.

- **Correspondence suite expanded to ~22 targets, 450+ `#guard` tests** across 19 correspondence
  files, with RunSte Rust tests added to `src/raft.rs`, `src/tracker.rs`, and elsewhere.

**No bugs found** in any modelled Rust function.  One **notable finding**: CI9–CI12 revealed
that `VotersLearnersDisjoint` as initially stated is *stricter* than the actual Raft
implementation — the demotion state allows a peer to be simultaneously in `outgoing` and
`learners_next`, which the strict 4-clause predicate incorrectly forbids.

---

## Proved Theorems

### `LimitSize.lean` — 25 theorems

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

### `CommittedIndex.lean` — 28 theorems

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

### `MaybeAppend.lean` — 19 theorems (includes 2 helpers)

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

### `Inflights.lean` — 50 theorems *(phase 5 — complete)*

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

### `HasQuorum.lean` — 20 theorems *(phase 5 — complete)*

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

### `QuorumRecentlyActive.lean` — 11 theorems *(phase 5 — complete)*

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

### `SafetyComposition.lean` — 10 theorems *(phase 5 — complete)*

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

### `RaftSafety.lean` — 10 theorems *(phase 5 — complete, 0 sorry)*

| Theorem | Level | Bug-catching | Status | Notes |
|---------|-------|-------------|--------|-------|
| `raft_state_machine_safety` (RSS1) | **High** | **High** | ✅ | Two quorum-committed entries at same index must be equal |
| `raft_safety_contra` (RSS1b) | **High** | **High** | ✅ | Contrapositive: distinct entries cannot both be committed |
| `raft_joint_state_machine_safety` (RSS2) | **High** | **High** | ✅ | Joint-config: same, via incoming quorum |
| `raft_joint_state_machine_safety_sym` (RSS2b) | **High** | **High** | ✅ | Joint-config: same, via outgoing quorum |
| `log_matching_property` (RSS3) | **High** | **High** | ✅ | Proved given `LogMatchingInvariantFor E logs` |
| `raft_committed_no_rollback` (RSS4) | **High** | **High** | ✅ | Proved given `NoRollbackInvariantFor E voters logs₀ logs₁` |
| `raft_leader_completeness_via_witness` (RSS5) | **High** | **High** | ✅ | Proved given explicit witness voter |
| `raft_cluster_safety` (RSS6) | **High** | **High** | ✅ | **End-to-end**: cluster safe given `hcert` |
| `raft_joint_cluster_safety` (RSS7) | **High** | **High** | ✅ | **End-to-end**: joint-config cluster safe given `hcert` |
| `raft_end_to_end_safety_full` (RSS8) | **High** | **High** | ✅ **PROVED** | Fully proved via `CommitCertInvariant` (r133) |
| `LogMatchingInvariantFor` (def) | **High** | **High** | ✅ | Generic E LMI predicate for RSS3 |
| `NoRollbackInvariantFor` (def) | **High** | **High** | ✅ | Generic E NRI predicate for RSS4 |

All 14 theorems proved (0 sorry). RSS8 was the last remaining sorry in the entire
FV suite; it is now closed via `raftReachable_cci` (RT1) in `RaftTrace.lean`, which
proves `CommitCertInvariant` holds for every reachable cluster state.

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

### `RaftProtocol.lean` — 10 theorems *(phase 5 — complete, 0 sorry)*

| Theorem | Level | Bug-catching | Status | Notes |
|---------|-------|-------------|--------|-------|
| `logMatchInvariant_constant` (RP1) | Mid | Medium | ✅ | Constant log functions trivially satisfy LMI |
| `rss3_from_logMatchInvariant` (RP2) | **High** | **High** | ✅ | RSS3 instantiated for specific voter pair |
| `matchTerm_implies_log_has_term` (RP3) | Mid | Medium | ✅ | If term matches, log has that term at that index |
| `maybeAppend_preserves_prefix` (RP4) | Mid | **High** | ✅ | Appended log preserves the conflict-point prefix |
| `rss4_from_noRollback` (RP5) | **High** | **High** | ✅ | RSS4 instantiated for specific log transition |
| `requestVote_no_log_change` (RP7) | Mid | Medium | ✅ | RequestVote messages do not modify logs |
| `appendEntries_preserves_log_matching` (RP6) | **High** | **High** | ✅ | **Full proof**: LMI maintained by AppendEntries (all 3 cases) |
| `raft_transitions_no_rollback` (RP8) | **High** | **High** | ✅ | No-rollback for single AppendEntries step given `hno_truncate` |
| `lmi_preserved_of_log_unchanged` | Mid | Low | ✅ | Helper: LMI trivially preserved if logs don't change |
| `lmi_preserved_of_leader_lmi` | **High** | **High** | ✅ | Core helper: leader LMI implies cluster LMI after append |

All 10 theorems proved (0 sorry). RP6 is the key result: all three AppendEntries cases
(§MatchFail, §NoConflict, §Conflict) are machine-checked. The §Conflict case uses a
`hleader_lmi` hypothesis expressing the Raft election-safety invariant. RP8 directly
models the Rust `assert!(conflict > committed)` panic-guard as a `hno_truncate`
hypothesis, proving the no-rollback property from it.

---

### `RaftTrace.lean` — 5 theorems *(phase 5 — complete, 0 sorry)*

| Theorem | Level | Bug-catching | Status | Notes |
|---------|-------|-------------|--------|-------|
| `initialCluster_cci` (RT0) | Mid | Medium | ✅ | Initial cluster satisfies CommitCertInvariant (vacuously) |
| `raftReachable_cci` (RT1) | **High** | **High** | ✅ | Every reachable state satisfies CCI (by induction on RaftReachable) |
| `raftReachable_safe` (RT2) | **High** | **High** | ✅ | **Top-level**: every reachable cluster state is safe |

`RaftTrace.lean` is the capstone file. It defines an inductive `RaftReachable` predicate
with a `step` constructor whose hypotheses capture the Raft protocol invariants:
- `hlogs'`: only one voter's log changes per step
- `hno_overwrite`: committed entries are not overwritten
- `hqc_preserved`: quorum-certified entries are preserved across all logs
- `hcommitted_mono`: committed indices only advance
- `hnew_cert`: new committed entries are quorum-certified

RT1 proves by structural induction that every `RaftReachable` state satisfies
`CommitCertInvariant`. RT2 composes RT1 with RSS8 (`raft_end_to_end_safety_full`).
Together they establish unconditional end-to-end cluster safety for all reachable states.

**Assessment**: The `step` constructor hypotheses are proof-engineering artefacts —
they precisely capture the conditions needed to preserve `CommitCertInvariant`, but do
not yet correspond to concrete Raft protocol transitions (message types, term management,
leader election). This is the honest residual gap: the proof architecture is complete and
machine-checked; the final step toward a fully concrete proof would require connecting
real Raft transitions to these abstract hypotheses.

---

## Critical Gap Analysis (from External Critique, 2026-04-20)

An independent critique has identified a **significant structural gap** in the current proof:
the `RaftReachable.step` constructor bundles 5 hypotheses as axioms that are never
discharged from a concrete protocol model.  These are not `sorry`-guarded in Lean (so they
appear as 0 sorry), but they represent informal assumptions rather than proved facts.

### Hypothesis-by-hypothesis status

| Hypothesis | What it requires | Existing support | Difficulty |
|---|---|---|---|
| `hlogs'` | Only one node's log changes per step | RP8 already models this for AppendEntries | **Low** — needs a message-delivery model |
| `hno_overwrite` | Committed entries aren't overwritten | CPS1 discharges this from `h_committed_le_prev` + CT2 | **Discharged** via CPS1 |
| `hqc_preserved` | Quorum-certified entries preserved in ALL logs | CPS13 discharges this given `CandidateLogCovers` via LC3/LC6 | **Conditionally discharged** via CPS13 |
| `hcommitted_mono` | Committed indices only advance | MC1 + CPS11a+11b prove this from `ValidAEStep` | **Discharged** via CPS11 |
| `hnew_cert` | Newly committed entries are quorum-certified | CR8 discharges this from `CommitRuleValid` (definitional) | **Discharged** via CR8 |

### The status of `hqc_preserved` (leader completeness)

**As of run 41/42**, this hypothesis is now conditionally discharged:

- **`RaftElection.lean`** — `NodeState` model with `currentTerm`/`votedFor` ✅
- **`electionSafety` (RE5)** — at most one leader per term ✅
- **`voteGranted` (RE7)** — vote granted → `isUpToDate` ✅
- **`leaderCompleteness` (LC3)** — winner has committed entries given `CandidateLogCovers` ✅
- **`hqc_preserved_from_leaderBroadcast` (LC6)** — discharge condition for `hqc_preserved` ✅
- **`validAEStep_hqc_preserved_from_lc` (CPS13)** — discharges `hqc_preserved` from
  `CandidateLogCovers` via `hasQuorum_monotone` + `LeaderCompleteness` ✅

**Remaining**: `CandidateLogCovers` is still taken as a hypothesis. Deriving it from a
concrete global election model (rather than from `CandidateLogCovers` as an explicit
precondition) is the final piece.

### Why the residual gap still matters

`raftReachable_safe` (RT2) reads:
> *"For any cluster state reachable by valid Raft transitions, no two nodes ever apply
>  different entries at the same log index."*

"Valid Raft transitions" now means states satisfying `ValidAEStep` — a concrete structure
whose fields are tied to real Rust conditions. The only remaining conditionality is that
`CandidateLogCovers` must be established from the full election model. This is a much
smaller gap than the original "no election model" situation.

### Recommended next target

| Priority | Target | Gap addressed | Difficulty |
|----------|--------|---------------|------------|
| **1** | Derive `CandidateLogCovers` from election reachability | Final `hqc_preserved` closure | Medium-high (20–40 theorems) |
| **2** | A6 integration: connect `MC4` to `ValidAEStep.hnew_cert` | Term-safety in commit rule | Medium |

---

## Gaps and Recommendations — Updated

~~The FV project is complete.~~ All previously identified gaps have been resolved; the
critical remaining work is the election model and concrete transition satisfaction.
The resolved gap list:

| Gap | Resolution | Run |
|-----|-----------|-----|
| RP6: LMI preservation by AppendEntries | Proved via `lmi_preserved_of_leader_lmi`, all 3 cases | r131 |
| RP8: No-rollback for AppendEntries | Proved given `hno_truncate` panic-guard | r131 |
| RSS8: End-to-end safety | Proved via `CommitCertInvariant` + `RaftTrace` induction | r133 |
| RT1: CCI inductive invariant | Proved by structural induction on `RaftReachable` | r133 |
| CMC6: acked → log entry bridge | Proved; CMC6 now machine-checked | r130 |
| RSS3/RSS4: incorrect formulation | Corrected with proper hypotheses and proved | r130 |

### Remaining open questions

1. **Connecting broadcast model to full Raft election protocol** (remaining gap): `AEBroadcastInvariant.lean`
   (ABI8, Run 49) now proves `hqc_preserved` after a sequential AE broadcast. The remaining gap
   is connecting this model to the full Raft election lifecycle: showing that after a real election
   (leader selected, term updated, vote granted), the leader actually performs the AE broadcast
   sequence that ABI8 requires. This needs ~20–40 theorems bridging `RaftElection.lean` to
   the `ValidAEStep` broadcast sequence.
2. **Term tracking**: integrating Raft term numbers into the concrete election model so that only
   entries from the current leader's term are committed. `MaybeCommit.lean` (MC4) proves term
   safety for `maybe_commit`; the remaining work is connecting this to the election model.
3. **`jointCommittedIndex` empty-config divergence**: Lean returns `0`, Rust returns `u64::MAX`.
   The `outgoing ≠ []` precondition is implicit but not enforced by type.
4. ~~**`makeLog_some` / `makeLog_none` sorry** (FindConflictCorrespondence.lean)~~ **✅ CLOSED (Run 55)**:
   `makeLog_some` proved using `indexInj_tail` + `no_double_idx` helpers with `List.mem_iff_get`
   and `getElem!_pos`; `makeLog_none` was already proved. **0 sorry remain.**

**Resolved since prior critique** (Runs 49–55):
- `AEBroadcastInvariant.lean`: ABI1–ABI10 proved; broadcast induction gap closed (ABI6).
- `hqc_preserved_of_broadcast` (ABI8): full broadcast → `hqc_preserved` without needing the election model.
- `FindConflictCorrespondence.lean`: 17 `#guard` correspondence tests all pass.
- `ra_batch_term` (P6): batch placement and term correctness for `RaftLog::append`.
- `ra_beyond_batch_none` (P7): no spurious trailing entries after `raftLogAppend`.
- `makeLog_some` (Run 55): proved via `indexInj_tail` + `no_double_idx` helpers. **0 sorry remain.**

---

## Trajectory to Completion

**Substantially complete** — all major milestones achieved; A5 concrete reachability gap remains:

| Step | Task | File | Status |
|------|------|------|--------|
| 1 | Define `RaftTransition` type (AppendEntries + RequestVote) | `RaftProtocol.lean` | ✅ Done (r129) |
| 2 | Prove `LogMatchingInvariantFor` maintained by AppendEntries (RP6) | `RaftProtocol.lean` | ✅ Proved (r131) |
| 3 | Prove `NoRollbackInvariantFor` maintained by single AppendEntries step (RP8) | `RaftProtocol.lean` | ✅ Proved (r131) |
| 4 | Define `RaftReachable` inductive type and prove CCI as invariant (RT1) | `RaftTrace.lean` | ✅ Proved (r133) |
| 5 | Close `raft_end_to_end_safety_full` (RSS8) | `RaftSafety.lean` | ✅ Proved (r133) |
| 6 | Top-level safety: `raftReachable_safe` (RT2) | `RaftTrace.lean` | ✅ Proved (r133) — **conditional** |
| 7 | `NodeState` model: terms, votedFor, term monotonicity | `RaftElection.lean` | ✅ Done (r141+) |
| 8 | `ElectionSafety`: at most one leader per term | `RaftElection.lean` | ✅ Proved (r141+) |
| 9 | `LeaderCompleteness`: elected leader has all committed entries | `LeaderCompleteness.lean` | ✅ Proved (r143+) |
| 10 | `ConcreteTransitions`: AppendEntries model + LMI/CandLogMatching proofs | `ConcreteTransitions.lean` | ✅ Proved (r148+) |
| 11 | `CommitRule`: discharge `hnew_cert` | `CommitRule.lean` | ✅ Proved (r155+) |
| 12 | A6 term safety: `maybe_commit` only commits from current term | `MaybeCommit.lean` | ✅ Proved (r157) |
| 13 | **A5 bridge**: `ValidAEStep` structure + CPS2 (`validAEStep_raftReachable`) | `ConcreteProtocolStep.lean` | ✅ Proved (r158) |
| **14** | **Broadcast induction**: `hqc_preserved` after full AE broadcast round | `AEBroadcastInvariant.lean` | ✅ **Proved** (r165, ABI8) |
| **15** | **Connect broadcast to election lifecycle**: leader after election → AE broadcast → ABI8 | **Future work** | **⬜ Remaining gap** |

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

- **`appendEntries_preserves_log_matching` (RP6) full proof** (finding #20) — all three cases
  (§MatchFail, §NoConflict, §Conflict) are machine-checked.  The §Conflict case uses
  `hleader_lmi` (leader entries are LMI-compatible with the cluster), capturing the Raft
  election-safety protocol invariant.  New helper: `lmi_preserved_of_leader_lmi`.

21. **`raft_transitions_no_rollback` (RP8) proved** — for a single AppendEntries step,
    given the `hno_truncate` panic-guard condition.  The proof is clean: show that for every
    committed entry at index `k`, `logs₁ w k = logs₀ w k` for all voters `w`, then use
    function extensionality to convert the quorum predicate.  The `hno_truncate` hypothesis
    directly models the Rust `assert!(conflict > committed)` invariant in `maybe_append`.

22. **`raftReachable_cci` (RT1) and `raftReachable_safe` (RT2)** — the capstone results.
    RT1 is a proof by structural induction that every cluster state reachable via valid
    Raft transitions satisfies `CommitCertInvariant`.  RT2 chains RT1 with RSS8 to obtain
    the unconditional top-level safety theorem: for *any* reachable cluster, no two nodes
    ever apply different entries at the same log index.  The `RaftReachable` inductive type
    provides a clean abstraction boundary: its `step` constructor makes the invariant
    preservation conditions explicit as typed hypotheses, preventing any informal reasoning
    from entering the proof.  RSS8 is now a clean two-line proof:
    ```lean
    theorem raft_end_to_end_safety_full [DecidableEq E] (hd : Nat) (tl : List Nat)
        (cs : ClusterState E) (hvoters : cs.voters = hd :: tl)
        (hcci : CommitCertInvariant cs) : isClusterSafe cs :=
      raft_cluster_safety hd tl cs hvoters
        (fun v k e ⟨hcomm, hlog⟩ => hcci v k e hcomm hlog)
    ```
    This is the most important result in the FV portfolio: machine-checked Raft safety.

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/fv-squad/actions/runs/23979949696) automated formal verification. Project complete: 443+ theorems, 0 sorry, 23 Lean files.

---

## New Findings Since Last Critique

### `RaftElection.lean` — 15 theorems (RE1-RE15)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `wonInTerm_nil` (RE1) | Low | Low | Vacuous quorum for empty voter list |
| `wonInTerm_iff` (RE2) | Low | Low | Definitional unfolding |
| `voteRecord_single_valued` (RE3) | Mid | **High** | One vote per voter per term — core Raft invariant |
| `shared_voter_of_two_winners` (RE4) | Mid | **High** | Two winners share a voter — key lemma for RE5 |
| `electionSafety` (RE5) | **High** | **High** | At most one winner per term — central Raft property |
| `electionSafety_ne` (RE6) | Mid | Medium | Alternative formulation of RE5 |
| `voteGranted_isUpToDate` (RE7) | Mid | **High** | If vote was granted, candidate was log-fresh |
| `voteGranted_priorVote_none_or_self` (RE8) | Mid | **High** | Single-vote-per-term check |
| `not_voteGranted_of_other_prior` (RE9) | Mid | **High** | Cannot vote for two different candidates |
| `voteGranted_and_prior_eq` (RE10) | Mid | Medium | Prior vote consistency |
| `wonInTerm_implies_some_voter` (RE11) | Low | Low | Winner implies ∃ voter — helper |
| `wonInTerm_singleton_iff` (RE12) | Low | Low | Singleton cluster correctness |
| `wonInTerm_singleton_self` (RE13) | Low | Low | Self-vote wins in singleton |
| `electionSafety_two_leaders` (RE14) | Mid | **High** | NodeID form of RE5 |
| `wonInTerm_voter_voted` (RE15) | Mid | Medium | Consistent ballot property |

**Assessment**: RE5 (`electionSafety`) is the highest-value theorem in this file.  It directly
formalises Raft §5.2 and closes a major gap in the top-level safety argument.  RE7-RE10 are
the vote-granting conditions that feed into `LeaderCompleteness.lean`.  This file is genuinely
useful: a bug in the Raft vote-handling code (e.g., allowing two winners in the same term)
would cause RE5 to fail.

### `LeaderCompleteness.lean` — 10 theorems (LC1-LC10)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `electionWinner_overlaps_commitQuorum` (LC1) | High | **High** | Quorum overlap — foundational step |
| `electionWinner_shared_voter` (LC2) | High | **High** | Corollary of LC1 |
| `leaderCompleteness` (LC3) | **High** | **High** | Main LC theorem (given CandidateLogCovers) |
| `leaderCompleteness_fullChain` (LC4) | **High** | **High** | Unique winner + has committed entries |
| `wonInTerm_implies_isUpToDate` (LC5) | Mid | **High** | Voter who voted → winner was log-fresh |
| `wonInTerm_voters_allUpToDate` (LC5b) | Mid | Medium | All voters → winner was log-fresh wrt each |
| `hqc_preserved_from_leaderBroadcast` (LC6) | **High** | **High** | Discharge condition for hqc_preserved |
| `candidateLog_of_logMatchingAndUpToDate` (LC7) | High | **High** | LMI + HLogConsistency → CandidateLogCovers |
| `leaderCompleteness_via_logMatching` (LC8) | **High** | **High** | Full LC given all three invariants |
| `leaderCompleteness_via_rss5` (LC-rss5) | High | Medium | Re-derives LC3 via RSS5 for coherence |

**Assessment**: `LeaderCompleteness.lean` is the most structurally important file added since
the original "COMPLETE" status was claimed.  It formalises the core of the Raft Leader
Completeness argument (§5.4.2) and explicitly isolates the remaining gap as `HLogConsistency`.
The key insight: `CandidateLogCovers` (the winner's log agrees with every voter who voted for
it) is sufficient to prove leader completeness, and `HLogConsistency` (isUpToDate + committed
entry → candidate has entry) is what a concrete protocol model needs to prove.

**Concern**: `HLogConsistency` is an explicit hypothesis — not a proved invariant.  Until it
is proved from a concrete AppendEntries model (A4/A5), `leaderCompleteness_via_logMatching`
(LC8) remains conditional.  The file is honest about this: all hypotheses are explicit, and
0 sorry is used.

**Positive finding**: `hqc_preserved_from_leaderBroadcast` (LC6) proves that if (a) the
leader has all committed entries (by leader completeness) and (b) AppendEntries puts the
leader's log entries into all voters' logs, then `isQuorumCommitted` is preserved across the
transition.  This is the correct formulation of `hqc_preserved` — it's about *quorum
preservation* (isQuorumCommitted in new state), not *universal log equality* (which is
stronger than what Raft guarantees).

---

### `ConcreteTransitions.lean` — 6 theorems (CT1-CT6), 0 sorry

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `hlc_of_candLogMatching` (CT1) | **High** | **High** | HLogConsistency from CandLogMatching + coverage; 0 sorry |
| `applyAE_preserves_prefix` (CT2) | Mid | **High** | AppendEntries preserves entries at indices ≤ prevLogIndex; 0 sorry |
| `applyAE_extends_at_entries` (CT3) | Mid | **High** | AppendEntries writes new entries at expected positions; 0 sorry |
| `lmi_preserved_single_step` (CT4) | High | **High** | Single AE step preserves LogMatchingInvariantFor; 0 sorry |
| `candLogMatching_of_broadcast` (CT5) | **High** | **High** | Leader broadcast → CandLogMatching; 0 sorry |
| `hlc_from_concrete_protocol` (CT6) | **High** | **High** | Delegates to CT1; 0 sorry |

**Assessment**: This is the A4 formal spec file.  Its primary contribution is **CT1**
(`hlc_of_candLogMatching`): a clean, machine-checked proof that `HLogConsistency` follows
from two concrete protocol obligations — `CandLogMatching` (extended log matching for the
candidate) and `CandLogCoversLastIndex` (the candidate's log agrees with each voter's log
at the voter's last index).

**CT1 reduces the A4/A5 gap** to two specific obligations that are each more tractable
than the original `HLogConsistency`:
- `CandLogCoversLastIndex` follows from isUpToDate + concrete log history (AppendEntries
  from prior leaders extend the log monotonically).
- `CandLogMatching` follows from the Log Matching Invariant (LMI) applied to
  candidate-follower log pairs (CT4 is the key step, proved with explicit hypotheses).

**CT2 and CT3** are fully proved and cover the core properties of `applyAppendEntries`:
prefix preservation and correct entry placement.  These are directly analogous to the
`MA5`/`MA6` theorems in `MaybeAppend.lean` (which proved the same for the term-level model).

**CT4 and CT5 are now fully proved** (0 sorry) with explicit hypotheses:
- CT4 (`lmi_preserved_single_step`): proved with `hprev` (leader log agrees at `prevLogIndex`)
  and `hcand_eq` (new entries come from leader's log).
- CT5 (`candLogMatching_of_broadcast`): proved with `hlog_none` (voter logs bounded by `lastIndex`)
  and `hcand_mono` (candidate log has no holes in its None-region).

These hypotheses capture the remaining A5 gap: establishing them from a concrete reachability
model would complete the fully self-contained proof.

**Positive finding**: the `AppendEntriesMsg` type and `writeEntries`/`applyAppendEntries`
functions defined here are a clean, entry-typed model of `maybe_append` that can serve as
the foundation for the remaining A5 work.  The `listGet?` helper avoids stdlib version
dependencies while remaining provably correct.

---

### `CommitRule.lean` — 9 theorems (CR1-CR9, 0 sorry)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `qc_from_quorum_acks` (CR1) | Mid | **High** | Quorum acks with entry → `isQuorumCommitted` |
| `qc_preserved_by_log_agreement` (CR2) | Mid | **High** | QC preserved when log positions unchanged |
| `qc_preserved_by_log_growth` (CR3) | Mid | **High** | QC preserved when entries at `k` kept/added |
| `matchIndex_quorum_qc` (CR4) | High | **High** | matchIndex quorum ≥ k with entries → QC |
| `commitRuleValid_implies_hnew_cert` (CR5) | **High** | **High** | `CommitRuleValid` → `hnew_cert` |
| `hnew_cert_of_qc_advance` (CR6) | High | **High** | QC-gated advance → `CommitRuleValid` |
| `qc_of_accepted_ae_quorum` (CR7) | High | **High** | Quorum of AE acceptors → `isQuorumCommitted` |
| `commitRuleValid_step_condition` (CR8) | **High** | **High** | `CommitRuleValid` ↔ `hnew_cert` (definitional) |
| `commitRule_and_preservation_implies_cci` (CR9) | **High** | **High** | Commit rule + log preservation → CCI preserved |

**Assessment**: CR8 is the most important theorem: `CommitRuleValid` is **definitionally equal**
to the `hnew_cert` hypothesis in `RaftReachable.step`.  This means a concrete Raft protocol
that uses the quorum-ACK commit rule directly satisfies the `RaftReachable.step` invariant
preservation conditions, enabling the full safety proof chain.  CR9 shows that
`CommitCertInvariant` is an inductive invariant under `CommitRuleValid` — the formal
expression of the Raft commit rule as a safety property.

---

### `MaybeCommit.lean` — 12 theorems (MC1-MC12, 0 sorry)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `maybeCommit_ge_committed` (MC1) | Mid | **High** | Committed never decreases (monotone) |
| `maybeCommit_or` (MC2) | Low | Low | Result is `committed` or `maxIndex` |
| `maybeCommit_advances_iff` (MC3) | Mid | **High** | Advances ↔ both conditions hold |
| `maybeCommit_term` (MC4) | **High** | **High** | **A6**: if advanced, `log[result] = some term` |
| `maybeCommit_no_advance_mismatch` (MC5) | Mid | **High** | Term mismatch → no advance |
| `maybeCommit_no_advance_le` (MC6) | Mid | Medium | `maxIndex ≤ committed` → no advance |
| `maybeCommit_eq_maxIndex` (MC7) | Mid | Medium | If advanced, result = `maxIndex` |
| `maybeCommit_le_max` (MC8) | Low | Low | Result ≤ `max committed maxIndex` |
| `maybeCommit_idempotent` (MC9) | Mid | Medium | Applying twice = applying once |
| `commitTo_ge_committed` (MC10) | Mid | **High** | `commit_to` is monotone |
| `commitTo_advances_iff` (MC11) | Mid | **High** | `commit_to` advances iff `toCommit > committed` |
| `maybeCommit_eq_commitTo` (MC12) | High | **High** | `maybeCommit` = `commitTo` when term check passes |

**Assessment**: **MC4 (`maybeCommit_term`)** is the most important theorem in this file — it is
the formal Lean proof of the **A6 term safety condition** (Raft §5.4.2).  It proves that
`RaftLog::maybe_commit` only advances the committed index to an index whose log entry has
the exact `term` used in the call (which is always the leader's current term in the Raft
protocol).  This prevents the "figure 8" problem: a stale entry from an old leader's term
cannot be directly committed by a new leader, because the new leader's `maybe_commit` call
would use its own current term, and the old entry would have a different term.

**MC4 + CR8 together** close both halves of the commit safety picture:
- **CR8**: the quorum-certification half — committed advances only when a quorum has the entry.
- **MC4**: the term-safety half — committed advances only when the entry's term = current term.

**MC1 (`maybeCommit_ge_committed`)** directly corresponds to the `hcommitted_mono` hypothesis
in `RaftReachable.step`, providing a concrete discharge proof.

**MC12** establishes that `maybeCommit` is exactly `commitTo` when the term check passes —
a clean decomposition showing that `maybe_commit` is `commit_to` with an A6 safety gate.

---

### `ConcreteProtocolStep.lean` — 14 theorems (CPS1-CPS14, 0 sorry)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `validAEStep_hno_overwrite` (CPS1) | **High** | **High** | Concrete discharge of `hno_overwrite`: `h_committed_le_prev` + CT2 |
| `validAEStep_raftReachable` (CPS2) | **High** | **High** | **Main bridge**: valid AE step on reachable → new reachable state |
| `validAEStep_hcand_eq_at_entry` (CPS3) | Mid | **High** | New entry in AE msg appears at correct log index |
| `validAEStep_prefix_unchanged` (CPS4) | Mid | **High** | Indices ≤ `prevLogIndex` unchanged by the step |
| `validAEStep_lmi_preserved` (CPS5) | **High** | **High** | Valid AE step preserves `LogMatchingInvariantFor` (CT4) |
| `validAEStep_hlc` (CPS6) | **High** | **High** | `CandLogMatching` before → `HLogConsistency` after (CT5b) |
| `validAEStep_new_entry_at` (CPS7) | Mid | Medium | Voter `v`'s log at `prevLogIndex+1+j` = msg entry `j` |
| `validAEStep_logs_v` (CPS8) | Mid | Medium | Voter `v`'s log is the updated AE-applied log |
| `validAEStep_logs_other` (CPS9) | Mid | Medium | Other voters' logs are unchanged |
| `twoStep_raftReachable` (CPS10) | **High** | **High** | Two consecutive valid AE steps: result is `RaftReachable` |
| `validAEStep_committed_mono_of_local` (CPS11a) | Mid | **High** | Local committed-indices of non-`v` voters unchanged |
| `validAEStep_committed_invariant` (CPS11b) | Mid | **High** | Committed invariant preserved by the step |
| `ae_step_no_rollback` (CPS12) | **High** | **High** | Global no-rollback: all voters' committed entries preserved |
| `validAEStep_hqc_preserved_from_lc` (CPS13) | **High** | **High** | **`hqc_preserved` discharge**: given `CandidateLogCovers`, QC entries preserved via `hasQuorum_monotone` + `LeaderCompleteness` |

**Assessment**: **CPS2 (`validAEStep_raftReachable`)** is the most architecturally important
theorem in this file and in the entire A5 trajectory.  It is the **first theorem in the
FVSquad project to directly connect a concrete protocol rule to the abstract `RaftReachable`
inductive**.  It proves: given any `RaftReachable cs` and a `ValidAEStep cs cs'`, the
resulting state `cs'` is also `RaftReachable`.

This means the project now has a formally verified path from:
```
Concrete AppendEntries step conditions (ValidAEStep)
         ↓  CPS2
Abstract RaftReachable.step hypotheses are satisfied
         ↓  RT1
CommitCertInvariant is preserved
         ↓  RT2 / raftReachable_safe
isClusterSafe cs'
```

**CPS1 (`validAEStep_hno_overwrite`)** directly discharges the `hno_overwrite` hypothesis
from `RaftReachable.step` using the concrete `h_committed_le_prev` field of `ValidAEStep`
combined with CT2 (preservation of entries ≤ `prevLogIndex`).  This gives a machine-checked
proof that the Rust panic guard `if conflict ≤ committed { fatal!("...") }` in `maybe_append`
is exactly the abstract hypothesis `hno_overwrite` in the safety proof.

**CPS12 (`ae_step_no_rollback`)** is a cluster-global version of the no-rollback property:
for every voter `u` (not just `v`), committed entries are preserved.

**CPS13 (`validAEStep_hqc_preserved_from_lc`)** (run 41) is the latest addition: it
discharges `hqc_preserved` from `CandidateLogCovers` using `hasQuorum_monotone` (HQ9) and
`leaderCompleteness` (LC3). This means the A5 path now has all five `RaftReachable.step`
hypotheses conditionally discharged from `ValidAEStep` fields, with only `CandidateLogCovers`
remaining as an external hypothesis rather than a concrete derivation.

**All five `RaftReachable.step` hypotheses** are now dischargeable from `ValidAEStep`:
- `hlogs'`: structural (one voter's log changes)
- `hno_overwrite`: CPS1 (via CT2 + `h_committed_le_prev`)
- `hqc_preserved`: CPS13 (via `CandidateLogCovers` + `hasQuorum_monotone` + LC3)
- `hcommitted_mono`: CPS11a/11b (via `commit_to` monotonicity)
- `hnew_cert`: CR8 (definitional equality with `CommitRuleValid`)

---

### `ElectionReachability.lean` — 12 theorems (ER1-ER12, 0 sorry)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `candLogCoversLastIndex_of_highWaterMark` (ER1) | **High** | **High** | HWM + CandLogMatching → CandLogCoversLastIndex; reduces key abstract obligation to a concrete point condition |
| `hlogConsistency_of_highWaterMark` (ER2) | **High** | **High** | HWM + CandLogMatching → HLogConsistency (required by LC7) |
| `candidateLogCovers_of_highWaterMark` (ER3) | **High** | **High** | HWM + VRC + voterIdx → CandidateLogCovers (unlocks CPS13) |
| `leaderCompleteness_of_highWaterMark` (ER4) | **High** | **High** | Full end-to-end: HWM → leaderCompleteness |
| `candLogMatching_of_extendedLMI` (ER5) | **High** | **High** | Extended LMI + hcand_eq → CandLogMatching (derives key condition from log-matching invariant) |
| `hwm_of_shared_entry` (ER6) | Mid | High | Shared entry at j ≥ voterIdx → HWM (concrete AE-round sufficient condition) |
| `hwm_of_lmi_and_candEntry` (ER7) | Mid | High | LMI + voter entry + cand entry at same j → HWM |
| `candidateLogCovers_of_extendedLMI` (ER8) | **High** | **High** | Extended LMI + hcand_eq + VRC + HWM → CandidateLogCovers (full chain) |
| `candLogCoversLastIndex_of_sharedSource` (ER9) | **High** | **High** | Shared source log R → CandLogCoversLastIndex (leader-origin sufficient condition) |
| `candidateLogCovers_of_sharedSource` (ER10) | **High** | **High** | Shared source → CandidateLogCovers (full chain via ER9) |
| `leaderCompleteness_of_sharedSource` (ER11) | **High** | **High** | Shared source → leaderCompleteness (complete end-to-end path from AE history) |
| `hwm_of_ae_prefix` (ER12) | **High** | **High** | AE prefix preservation: prior agreements survive AE step (inductive invariant for HWM) |

**Assessment**: `ElectionReachability.lean` (Run 43) is the most architecturally significant
file added since CPS2.  It provides **two independent sufficient conditions** for
`CandidateLogCovers` — the last remaining hypothesis in the fully self-contained proof chain:

1. **The high-water mark path** (ER1–ER8): reduces `CandidateLogCovers` to the existence
   of a single "agreement point" index `j ≥ voterIdx` at which the candidate's log matches
   the voter's.  This is exactly what the AE mechanism guarantees — after the leader broadcasts
   AE with `prevLogIndex = j`, every accepting voter's log agrees with the leader at `j`.
   The chain ER5 → ER6/ER7 → ER3 → CPS13 → CPS2 → RT1 → RT2 gives a fully specified
   reduction of `raftReachable_safe` to: (a) `hcand_eq` (the election model ensures the
   candidate was a valid voter), (b) a `LogMatchingInvariantFor` that extends to the
   candidate, and (c) an AE step that provides an agreement point at or above `voterIdx`.

2. **The shared-source path** (ER9–ER11): if there exists a reference log `R` such that
   both the candidate's log and every voter's log are prefixes of `R`, then
   `CandidateLogCovers` holds unconditionally.  This is the most natural and direct encoding
   of what happens in a concrete Raft protocol: after the leader sends AE messages, both
   the leader's log and the accepting voters' logs are prefixes of the leader's own log.

3. **The inductive invariant** (ER12): `hwm_of_ae_prefix` proves that if a high-water mark
   agreement point exists before an AE step, it is still valid after (the AE step preserves
   prior agreement points).  This is the inductive step needed to carry the HWM condition
   across protocol rounds.

**Remaining gap** (after ER1–ER12): The proof obligation now reduces to showing that,
after a concrete Raft election, there exists such a reference log `R` (or equivalently,
that the extended log-matching invariant holds with the candidate treated as a voter).
This is a global protocol-state property that requires connecting the AE round history
to the current state.  Roughly 5–15 additional theorems in a new file (e.g.,
`ElectionConcreteModel.lean`) would close this gap entirely.

**All 12 ER theorems** have bug-catching potential rated **High** because they directly
exercise the core conditions that prevent log divergence after elections.  A flaw in the
AE protocol's prefix-preservation or the vote-granting rule would cause at least one of
ER3, ER8, ER10, or ER11 to fail.

---

### `RaftLogAppend.lean` — 19 theorems (RA1-RA9 + 2 helpers + P4/P5/P6/P7 + 3 private helpers, 0 sorry)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `taa_entries_nonempty` (HTAA1) | Low (helper) | Low | `truncateAndAppend` with non-empty terms produces non-empty entries; scaffolding for HTAA2 |
| `taa_maybeLastIndex` (HTAA2) | Mid (helper) | Medium | Last index after `truncateAndAppend` = `after + newTerms.length - 1`; key arithmetic lemma for RA3/RA9 |
| `ra1_empty_noop` (RA1) | Mid | Medium | Empty batch is a no-op; catches implementations that mutate the log on empty input |
| `ra2_return_is_lastIndex` (RA2) | Mid | Medium | Return value equals `raftLastIndex` of the updated log; structural consistency check |
| `ra3_return_lastEntry` (RA3) | Mid | **High** | Non-empty no-gap batch: returned index = first.index + batch.length − 1; catches off-by-one errors in last-index computation |
| `ra4_committed_unchanged` (RA4) | Mid | **High** | `committed` is never modified by `raftLogAppend`; would catch any mutation of the committed index |
| `ra5_stableLastIdx_unchanged` (RA5) | Mid | Medium | `stableLastIdx` is read-only in `append`; structural check |
| `ra6_snapshot_preserved` (RA6) | Mid | Medium | Pending snapshot not modified by appending entries; verifies snapshot isolation |
| `ra7_committed_below_return` (RA7) | Mid | **High** | With `committed < first.1` (panic guard), returned index is strictly above `committed`; directly formalises the invariant enforced by `fatal!` in `src/raft_log.rs:393` |
| `ra8_empty_lastIndex_stable` (RA8) | Low | Low | Empty-batch corollary; degenerate sanity check |
| `ra9_return_is_batch_last` (RA9) | Mid | Medium | Named alias of RA3; documents the informal-spec post-condition P3 |
| `taa_maybeTerm_before` (P5-lemma) | **High** | **High** | `truncateAndAppend` preserves `maybeTerm` at every index strictly below `after`; directly proves log monotonicity. Would catch any implementation that over-truncates the unstable segment |
| `ra_prefix_preserved` (P5) | **High** | **High** | `raftLogAppend` preserves unstable `maybeTerm` for indices before the batch start; full P5 proof |
| `ra_committed_prefix_preserved` (P4) | **High** | **High** | Entries at indices ≤ `committed` are not touched by `raftLogAppend`; machine-checked analogue of the `fatal!` panic guard |
| `ra_batch_term` (P6) | **High** | **High** | Each batch entry appears at the expected index with its correct term; catches off-by-one in batch placement and term assignment |
| `ra_beyond_batch_none` (P7) | **High** | **High** | No entries exist beyond the last batch entry; proves the append is exact — no spurious trailing entries |

**Assessment**: `RaftLogAppend.lean` (Runs 45–50) covers the full public API of `RaftLog::append`
as formalised in `src/raft_log.rs`.  The most architecturally significant results are the
**prefix-preservation theorems** (P4/P5, Run 46) and the **batch exactness theorems** (P6/P7, Run 50):

- **P4** (`ra_committed_prefix_preserved`) directly validates the design intent of
  the `if after < committed { fatal!(...) }` guard in `raft_log.rs:393`: when the guard is
  satisfied, no committed entry is ever modified.
- **P5** (`ra_prefix_preserved`) proves that `raftLogAppend` never touches entries at indices
  strictly below the batch start — full prefix preservation.
- **P6** (`ra_batch_term`) proves that each batch entry lands at the correct index with the
  correct term — catches off-by-one errors in batch placement.
- **P7** (`ra_beyond_batch_none`) proves the append is exact — no spurious trailing entries exist
  after the last batch entry.

Together P4–P7 give complete postcondition coverage for `RaftLog::append`:  the resulting
log has exactly the right entries at exactly the right indices, with committed entries
untouched.

**Modelling approximations**: Entry payloads are omitted (only index/term modelled);
`u64` is replaced by `Nat` (no overflow); the panic path is not modelled.

---

### `ElectionConcreteModel.lean` — 8 theorems (ECM1-ECM7+ECM5b, 0 sorry)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `candLogCoversLastIndex_of_hae` (ECM1) | **High** | **High** | `CandLogCoversLastIndex` from `hae` via ER9 with R = candLog; simplest shared-source path |
| `candLogMatching_of_hae` (ECM2) | **High** | **High** | `CandLogMatching` from `hae` + log-boundary conditions via CT5; connecting broadcast log-agreement to abstract election predicate |
| `candidateLogCovers_of_hae` (ECM3) | **High** | **High** | `CandidateLogCovers` from `hae` + ECM1 + ECM2 + `hconsist`; full chain to the `hqc_preserved` discharge condition |
| `hqc_preserved_of_hae` (ECM4) | **High** | **High** | `hqc_preserved` from `hae` + `ValidAEStep` via CPS13 ∘ ECM3; primary export for the step-level proof |
| `hae_of_validAEStep` (ECM5) | **High** | **High** | Single AE step gives voter agreement at AE-covered indices; directly bridges `ValidAEStep` to the `hae` hypothesis |
| `hae_other_of_validAEStep` (ECM5b) | Mid | Medium | Non-target voters' logs unchanged by AE step; structural stability check |
| `hqc_preserved_of_validAEStep` (ECM6) | **High** | **High** | **Full composition theorem**: `ValidAEStep` + `hwin` + `hae` → `hqc_preserved`. Primary export; closes the last open gap in the `RaftReachable.step` proof chain |
| `sharedSource_of_hae` (ECM7) | Mid | Low | Documentation: makes the shared-source reference `R = candLog` explicit; re-states ECM1's existential for CORRESPONDENCE.md audit |

**Assessment**: `ElectionConcreteModel.lean` (Run 46) is architecturally the most significant
file since `ConcreteProtocolStep.lean`.  It provides the concrete election model that
closes the last open gap in the full Raft safety proof chain.

**The central result is ECM6** (`hqc_preserved_of_validAEStep`), which is a complete
composition theorem:

```
Concrete election model conditions (hwin, hae, hconsist)
         +  Valid AE step (ValidAEStep)
         ↓  ECM3 + ECM4
CandidateLogCovers holds
         ↓  CPS13
hqc_preserved holds
         ↓  CPS2
RaftReachable.step hypotheses all discharged
         ↓  RT1 → RT2
raftReachable_safe (isClusterSafe)
```

The key insight formalised here is the **shared-source argument**: after an election where
candidate `lead` wins and voters agree via AE broadcast, the leader's own log `leadLog` serves
as the natural shared reference log `R` in the ER9/ER10 condition.  The condition `hae`
(every voter's log agrees with the leader's up to the voter's last accepted index) is exactly
what a concrete AE broadcast step delivers — formally captured by ECM5.

**Remaining gap after ECM1–ECM7**: The `hae` hypothesis itself still needs to be derived by
induction over the AE broadcast history (showing that after the leader broadcasts to all
voters, every voter has accepted entries up to the leader's `nextIndex`).  This is the
`AEBroadcastInvariant.lean` target identified in TARGETS.md.  Roughly 10–20 theorems in
a new file would close this final gap, making the entire proof chain unconditional from
concrete Raft protocol mechanics.

**Bug-catching potential**: ECM1–ECM7 are all rated **High** for bug-catching because they
directly exercise the election-safety core.  A flaw in the Raft election logic (wrong
vote-counting, incorrect log comparison, AE prefix miscalculation) would cause at least
ECM3, ECM4, or ECM6 to fail.  ECM5 is particularly notable: it directly proves that
`ValidAEStep.hcand_eq` is exactly the `hae` condition needed — a mismatch between the
concrete AE protocol and the abstract election model would be caught here.

---

### `AEBroadcastInvariant.lean` — 10 theorems (ABI1-ABI10, 0 sorry)

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `hae_for_voter_after_ae` (ABI1) | High | High | After AE to voter `v` with `prevLogIndex=0`, `hae` holds for `v`; directly exercises the AE protocol step |
| `hae_for_voter_of_validAEStep` (ABI2) | High | High | Generalises ABI1 to any `ValidAEStep`; confirms hae preservation for target voter |
| `hae_for_other_preserved` (ABI3) | Mid | Medium | AE to `v` leaves `hae` intact for `w ≠ v`; structural stability — catches AE side-effects on non-target voters |
| `haeCovered_extend` (ABI4) | Mid | Medium | One AE step extends the covered-voter predicate by one; inductive step lemma |
| `haeCovered_nil` (ABI5) | Low | Low | Base case: empty coverage vacuously holds |
| `haeCovered_induction` (ABI6) | **High** | **High** | **Induction theorem**: after broadcasting to the first `n` voters, `hae` holds for all `n`; closes broadcast induction gap |
| `hae_of_two_voter_broadcast` (ABI7) | High | High | Specialisation to 2-voter clusters; concrete sanity check for the induction |
| `hqc_preserved_of_broadcast` (ABI8) | **High** | **High** | **Primary result**: full broadcast → `hqc_preserved`; composition of ABI6 + ECM4; the last missing link in the end-to-end proof chain |
| `hae_broadcast_invariant_schema` (ABI9) | High | High | General schema for arbitrary-length voter sequences; most general statement of the broadcast invariant |
| `hae_of_single_broadcast` (ABI10) | Mid | Medium | Specialisation to 1-voter clusters; base-case sanity check |

**Assessment**: `AEBroadcastInvariant.lean` (Run 49) is the most architecturally significant
file since `ElectionConcreteModel.lean`.  It closes the broadcast induction gap that ECM5
left open — ECM5 proved `hae` for a *single* AE step to *one* voter; ABI5 proves it for the
*full* broadcast sequence to *all* voters.

**The central result is ABI8** (`hqc_preserved_of_broadcast`), which extends ECM6 to the
broadcast setting:

```
Leader wins election (hwin) + valid AE broadcast to all voters (ValidAEStep sequence)
           ↓  ABI6 (haeCovered_induction)
  hae holds for all voters in the broadcast sequence
           ↓  ECM4 (hqc_preserved_of_hae)
hqc_preserved holds for the resulting cluster state
```

**Bug-catching potential**: ABI8 and ABI6 are rated **High** because the broadcast induction
is the most likely place for a subtle protocol bug to hide.  A flaw in the AE ordering
(wrong `prevLogIndex`, leader log mutation mid-broadcast, voter list divergence) would
break the ABI3/ABI4 preservation step and cause ABI6 to fail.

**Modelling approximations**: The broadcast is modelled as a sequential list of `ValidAEStep`
transitions, each with `prevLogIndex=0` (i.e., full-log AE).  The Rust code may send
incremental AE (from the last acknowledged index); the Lean model is a conservative
approximation (full-log AE is more expensive but semantically equivalent for `hae`
since it only *adds* agreement, never removes it).

---

### `FindConflictCorrespondence.lean` — 4 theorems + 17 `#guard` tests (0 sorry)

| Item | Level | Bug-catching potential | Notes |
|------|-------|----------------------|-------|
| `makeLog_some` (theorem, ✅ proved Run 55) | Low | Low | Helper: `makeLog stored idx` returns the stored term when `(idx, t)` ∈ `stored`; proved via `indexInj_tail` + `no_double_idx` using `List.mem_iff_get` + `getElem!_pos` |
| `makeLog_none` (theorem, ✅ proved) | Low | Low | Helper: `makeLog stored idx` returns `none` when `idx ∉ dom(stored)`; proved by induction |
| `indexInj_tail` (private helper, ✅ proved Run 55) | Low | Low | Derives `IndexInjective` for the tail from a cons list; key inductive step |
| `no_double_idx` (private helper, ✅ proved Run 55) | Low | Low | Two positions with the same first component cannot coexist; derives contradiction via `IndexInjective` |
| 17 `#guard` assertions | Mid | **High** | Compile-time correspondence tests: `findConflict (makeLog stored) entries = expected` for 17 concrete cases; all pass |

**Assessment**: The file's primary value is the 17 `#guard` tests, not the helper
theorems.  The `#guard` tests demonstrate that the Lean `findConflict` model agrees with
the Rust `RaftLog::find_conflict` implementation on all 17 correspondence cases (empty
entries, all-match, suffix conflict, new entries beyond log, etc.).  This is Task 8 Route B
evidence — direct behavioural correspondence without needing Aeneas extraction.

**Run 55 achievement**: The `makeLog_some` theorem was the last remaining `sorry` in the
project (until Run 60 adds ReadOnly.lean with RO8).

**Gaps**: The 17 cases cover the main behaviours but do not exercise:
- Logs with more than ~5 entries (performance limitation of `#guard`)
- Cases where `prevLogIndex > 0` (non-zero base index)
- Error handling paths (Rust returns `Result`; Lean models `Option`)

---

## Layer 8: Correspondence Validation (Runs 52–57)

Task 8 Route B correspondence tests provide direct behavioural evidence that Lean
implementation models agree with Rust source code on concrete inputs.  11 correspondence
files have been added (Runs 52–57), covering 11 distinct Rust functions with 152+ `#guard`
assertions and matching Rust unit tests (`cargo test correspondence`).

### Assessment of Layer 8 as a whole

**Strengths**:
- Each `#guard` test is a compile-time assertion checked by Lean's kernel — not a runtime
  test that could pass under a type error.
- The corresponding Rust unit tests (`test_*_correspondence` in `src/`) run against the
  actual implementation on the same fixture data, providing a true cross-check.
- Together, the 11 correspondence files cover the most critical data-path functions:
  log access (`find_conflict`, `maybe_append`, `is_up_to_date`), quorum operations
  (`committed_index`, `tally_votes`, `vote_result`, `has_quorum`), and utility functions
  (`limit_size`, `config_validate`, `inflights`, `log_unstable`).

**Limitations**:
- `#guard` tests are bounded to small inputs (compile-time evaluation has practical limits).
- All 11 correspondence tests show agreement — no divergence was found.  This is positive
  but also means we have not yet discovered any correspondence mismatches.
- Several files use `abstraction` level (not `exact`): `committed_index` only tests the
  non-group-commit path; `limit_size` uses `Nat` for sizes; `inflights` uses `List` for the
  ring buffer.

| File | Guards | Correspondence level | Key function |
|------|--------|---------------------|-------------|
| `FindConflictCorrespondence.lean` | 17 | Exact | `find_conflict` |
| `MaybeAppendCorrespondence.lean` | 35 | Exact | `maybe_append` |
| `IsUpToDateCorrespondence.lean` | 14 | Exact | `is_up_to_date` |
| `CommittedIndexCorrespondence.lean` | 13 | Abstraction | `committed_index` (non-GC) |
| `VoteResultCorrespondence.lean` | 17 | Exact | `vote_result` |
| `HasQuorumCorrespondence.lean` | 17 | Exact | `has_quorum` |
| `LimitSizeCorrespondence.lean` | 12 | Abstraction | `limit_size` |
| `ConfigValidateCorrespondence.lean` | 14 | Exact | `config_validate` |
| `InflightsCorrespondence.lean` | 14 | Abstraction | `Inflights` ring buffer |
| `LogUnstableCorrespondence.lean` | 14 | Exact | `log_unstable` ops |
| `TallyVotesCorrespondence.lean` | 12 | Exact | `tally_votes` |

**Bug-catching potential**: **High**.  Any change to the Rust implementation that modifies
observable input-output behaviour would cause the corresponding `#guard` tests to fail at
build time in CI.  This is a regression safety net stronger than the property-based theorems
for the specific functions covered.

---

## Layer 9: ReadOnly.lean (Run 60)

### `ReadOnly.lean` — 12 theorems, 1 sorry

Formalises the `ReadOnly` struct from `src/read_only.rs` — the leader-side bookkeeping
for the ReadIndex linearisability protocol (Raft §6.4).

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `RO1_addRequest_idempotent` | Mid | **High** | Duplicate context is silently ignored — catches any code that processes the same request twice |
| `RO2_addRequest_extends_queue` | Low | Medium | Queue grows by exactly 1 for new context |
| `RO3_addRequest_extends_pending` | Low | Medium | Pending map grows by correct entry |
| `RO4_addRequest_entry_present` | Mid | **High** | New entry retrievable with correct index and selfId; would catch wrong initial ack set |
| `RO5_recvAck_none_iff_absent` | Mid | **High** | Returns `none` exactly when ctx absent — catches silent failure to track acks |
| `RO6_recvAck_adds_id` | Mid | **High** | Ack set grows by id; prior acks preserved — catches lost-ack bug |
| `RO7_advance_noop_if_absent` | Mid | Medium | No-op when ctx not in queue — precondition safety |
| `RO8_advance_removes_ctx` (**sorry**) | Mid | **High** | After advance, ctx no longer in queue — requires NoDuplicates invariant |
| `RO9_inv_empty` | Low | Low | Empty state satisfies invariant — base case |
| `RO10_inv_add` | Mid | **High** | Invariant preserved by addRequest — key inductive step |
| `RO11_addRequest_count` | Low | Medium | pendingReadCount + 1 for new ctx |
| `RO12_pendingReadCount_zero_iff` | Low | Low | Zero count ↔ empty queue |

**Assessment**: The ReadOnly model captures the core linearisability safety protocol:
a read is not delivered until a quorum has acked the heartbeat at the commit index
captured when the request was received.  The theorems cover the key state transitions.

**Remaining sorry (RO8)**: `advance` should remove the delivered contexts from the queue.
The proof requires the `NoDuplicates queue` invariant (maintained by `addRequest`'s
idempotency guard but not yet formally stated as a separate invariant).  This is a
straightforward Task 5 target: state `NoDuplicates` as an invariant, show it is preserved
by `addRequest` and `advance`, then use it to prove `RO8`.

**Bug-catching potential**: The model catches bugs where:
- A duplicate read request is processed (RO1)
- An acknowledgement is double-counted (RO6)
- Read delivery is triggered before a quorum has responded (the `advance` function
  correctly dequeues all requests up to the acked context, providing FIFO linearisability)

**Approximations / Limitations**:
- The `req : Message` field is elided — payload correspondence not checked
- `Vec<u8>` context keys are modelled as `Nat` — no byte-level reasoning
- `ReadOnlyOption` (Safe vs LeaseBased) is not modelled

---

> *This section reviews `formal-verification/paper/paper.tex` as a critical reader.*

### Overall Impression

The paper is well-structured and makes a clear contribution.  The abstract accurately
describes what was proved and is honest about the human involvement.  The architecture
description (seven-layer, stdlib-only, 471 theorems, 0 sorry) is consistent with the
actual Lean artefacts.

### Accuracy Assessment

**File inventory table** (`tab:inventory`): stale as of Run 48.  The table reflects 29 files
and 471 theorems (Run 41).  Three new files need to be added:
- `ElectionReachability.lean` (12 theorems, Run 43)
- `RaftLogAppend.lean` (14 theorems, Run 45–46)
- `ElectionConcreteModel.lean` (8 theorems, Run 46)
The total is now **505 theorems across 32 files**.

**Layer summary table** (`tab:layers`): stale.  The `Layer 2: 119 theorems` entry is
incorrect; the current count for the 7 Layer-2 files is 139 theorems.  The three new files
(ElectionReachability, RaftLogAppend, ElectionConcreteModel) form a new Layer 8 or extend
Layer 7.  **Recommend adding** Layer 8 with 34 theorems (12 + 14 + 8) and updating totals.

**Run count**: The paper says "39 runs" at the time of writing.  As of Run 48, it should
say 48 runs.  **Recommend updating** throughout.

**Cost estimate**: `$280 (39 runs at ~$7 each)` should be updated to `~$336 (48 runs at ~$7 each)`.

**Abstract claim check**:
- "473 theorems across 29 Lean 4 files, stdlib only, 0 sorry" — *stale*; update to **505 theorems, 32 files**.
- "raftReachable_safe — no two nodes ever apply different log entries at same index" ✅
- "A5 bridge (validAEStep_raftReachable) proved" ✅
- "One formulation bug caught" ✅ (RSS3/RSS4)
- "No implementation bugs found" ✅
- **New claim to add**: "ElectionConcreteModel.lean (ECM1–ECM7, Run 46) closes the `hqc_preserved` gap conditional on `hae`: ECM6 (`hqc_preserved_of_validAEStep`) proves that a valid AE step from the elected leader preserves quorum-committed entries."
- **New claim to add**: "RaftLogAppend.lean (RA1–RA9+RA-PFIX1–3, Run 45–46) formally proves that `RaftLog::append` never touches committed entries (RA-PFIX3) and returns the correct last index (RA3)."

### Completeness Assessment

**Positive**:
- All seven original layers described with concrete theorem examples
- `hno_overwrite` discharge via CPS1 explained and connected to Rust source
- Formulation bug section is thorough and honest
- ECM6 closes the `hqc_preserved` gap (conditional on `hae`)

**Missing or underdeveloped** (updated for Run 48):
- **ElectionReachability.lean** (ER1–ER12) and **ElectionConcreteModel.lean** (ECM1–ECM7)
  are not yet reflected in the paper.  These are the two most significant architectural advances
  since CPS2.  The paper should add a new §5.2 section ("Closing the hqc_preserved Gap")
  describing:
  (a) ER1–ER12 (two sufficient conditions: HWM path and shared-source path);
  (b) ECM1–ECM7 (concrete election model: `hae` → `CandidateLogCovers` → `hqc_preserved`);
  (c) ECM6 as the current state of the gap closure (conditional on `hae`); and
  (d) the remaining obligation: deriving `hae` by induction over the AE broadcast history
      (target: `AEBroadcastInvariant.lean`, ~10–20 additional theorems).
- **RaftLogAppend.lean** (RA1–RA9+RA-PFIX1–3) should appear as a new §4.2 or §5.3 section
  documenting the formal verification of `RaftLog::append` including the committed-prefix
  preservation result (RA-PFIX3).
- **MC4 / A6 term safety** could be highlighted more prominently.  MC4
  (`maybeCommit_term`) is the formal proof of Raft §5.4.2 — the "figure 8" problem
  prevention.  This is arguably the most important result in Layer 7 alongside CPS2,
  yet it receives less emphasis than CPS2 in the paper's discussion.
- **CR8** (`CommitRuleValid ↔ hnew_cert`) is mentioned but its significance as a
  *definitional* proof step (closing an abstract step hypothesis without any proof
  obligations beyond unfolding definitions) could be better explained to readers
  unfamiliar with Lean.

### Clarity Concerns

- §4.1 (Target Selection) says Layer 3 has "~59 theorems" — after fixing the Layer 2
  count the tilde can be removed for Layer 3 (exact count is 59).
- The relationship between `validAEStep_raftReachable` (CPS2) and the abstract
  `RaftReachable.step` hypotheses is clear in §5.1 but could benefit from a
  one-sentence summary at the start of §4.1.7 connecting the concrete ValidAEStep
  fields to the five abstract step hypotheses.
- The "Note on authorship and voice" section (before Introduction) uses "Claude Opus 4.6"
  but the actual model used is Claude Sonnet 4.6 — this should be corrected.

### Intellectual Honesty

The paper is appropriately honest about what is and is not proved.  The `sorry`-count
disclosure (0 sorry) is accurate.  The correspondence limitations (CORRESPONDENCE.md) are
acknowledged in §4.3.

After Run 46, the `hqc_preserved` gap is substantially narrowed: ECM6 proves `hqc_preserved`
conditional on `hae`.  The paper should update its gap description from "roughly 20–40
additional theorems are needed" to "roughly 10–20 additional theorems (AEBroadcastInvariant.lean)
would close this entirely, with the `hae` hypothesis as the only remaining assumption."

### Recommendation

The paper needs the following targeted updates (in priority order):
1. **Update theorem count and file count**: 473 → 505 theorems, 29 → 32 files.
2. **Add new Layer 8 section** covering ElectionReachability (12T), RaftLogAppend (14T),
   and ElectionConcreteModel (8T) — 34 theorems total.
3. **Add §5.2 "Closing the hqc_preserved Gap"**: describe ECM6 and the remaining `hae`
   obligation; update gap estimate to ~10–20 theorems.
4. Fix Layer 2 theorem count in `tab:layers`: 119 → 139.
5. Update run count: 44 → 48.
6. Correct model name: "Claude Opus 4.6" → "Claude Sonnet 4.6".
7. Update cost estimate: $280 → ~$336.

---

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24697924459)
> automated formal verification. Current state: **505 theorems, 0 sorry, 32 Lean files**.
> Run 48: Task 7 (Proof Utility Critique) — RaftLogAppend.lean (14T) and ElectionConcreteModel.lean (8T) sections added, Paper Review updated, counts updated to 505.

---

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24702950218)
> automated formal verification. Current state: **526 theorems, 0 sorry, 37 Lean files**.
> Run 55: Task 5 (Proof Assistance — `makeLog_some` proved, 0 sorry achieved) + Task 7 (Critique update).

---

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24714321754)
> automated formal verification. Current state: **45 files, 493 theorem declarations, 1 sorry (RO8 in ReadOnly.lean)**.
> Run 60: Task 4 (ReadOnly.lean — ReadIndex protocol bookkeeping, 12 theorems, 1 sorry) +
> Task 7 (Critique update — Layer 8 correspondence validation table, Layer 9 ReadOnly section).

---

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24719296210)
> automated formal verification. Current state: **46 files, 540 theorem declarations, 0 sorry**.
> Run 64: Task 5 (Proof Assistance — RO8 proved, final sorry eliminated) +
> Task 7 (Critique update — Layer 9 ReadOnly Phase 5 completion, sorry count reaches zero project-wide).

## Run 64 Critique Update

### Task 5: RO8 Proved — Project Reaches 0 Sorry

Run 64 eliminated the project's last `sorry`: **RO8** (`RO8_advance_removes_ctx`) in
`ReadOnly.lean`.  The proof required:

1. **`ro8_aux_mem_take` (private helper)**: By induction on `l`, if
   `l.findIdx? (· == ctx) = some i` then `ctx ∈ l.take (i+1)`.  The key tactic
   was `by_cases hcond : (x == ctx) = true` / `rw [if_pos hcond]` / `rw [if_neg hcond]`
   for Bool case splits (note: `split_ifs` is not available in Lean 4.28 stdlib-only builds).

2. **RO8 main proof**: Added `hnd : ro.queue.Nodup` hypothesis.  Derived the
   `findIdx?` result via case analysis, applied the helper to show `ctx ∈ queue.take(i+1)`,
   then used `List.nodup_append` on the `take/drop` split to derive a contradiction from
   `ctx ∈ take` and `ctx ∈ drop`.

3. **RO13** (`RO13_addRequest_preserves_nodup`): New theorem proving `addRequest`
   preserves the Nodup invariant on the queue (given `QueuePendingInv`).  This closes
   the inductive cycle: RO13 establishes Nodup; RO8 uses Nodup to prove advance removes ctx.

**Lean 4.28 pitfall**: `subst` on `h : b = ctx` where both are free variables may
substitute the theorem parameter (`ctx`) rather than the locally bound variable (`b`).
Safe workaround: use `rw [h]` to change the goal without eliminating either variable,
then reference the parameter by name in subsequent steps.

### Task 7: Layer 9 (ReadOnly) — Phase 5 Complete

The ReadOnly module is now **Phase 5 (fully proved)**:
- **13 theorems**: RO1–RO12 + RO13, all proved, 0 sorry
- **16 guard tests**: compile-time correspondence tests all pass
- **Nodup invariant**: fully established inductively (RO13 + RO8)
- **advance correctness**: both directions proved (RO7: no-op when absent; RO8: removes ctx when present with Nodup)

### Project-Wide Sorry Count: 0

The project has reached **0 sorry** across all 46 Lean files and 540 theorems.  This
milestone is significant: every theorem in the FV suite is now type-checked by Lean
without any deferred obligations.

### Critique of the RO8 Proof

**Proof utility**: High.  `advance` is the critical operation in Raft's read-only
optimisation path.  The `advance_removes_ctx` property is the key safety invariant
ensuring that `advance` does not silently drop contexts that still need to be served.

**Nodup hypothesis**: The dependency on `ro.queue.Nodup` is explicit and honest.  The
complementary theorem (RO13) establishes that `addRequest` preserves Nodup (given
`QueuePendingInv` and that the context is fresh), completing the invariant cycle.
Maintainers should be aware that callers of RO8 must supply the Nodup proof.

**Correspondence gap**: The Lean `advance` model uses `findIdx?` (first occurrence
semantics).  The Rust `raft-rs` implementation uses a context ID to locate the entry
in a `VecDeque`, which may have different duplicate handling.  If the Rust implementation
can ever produce a queue with duplicate context IDs (e.g., via a race), the Lean model
may diverge.  This is acknowledged in CORRESPONDENCE.md.

**Recommendations**:
- Consider a runtime assertion in the Rust code (`debug_assert!(!queue.contains(&ctx))`
  before insertion) to guarantee the Nodup property that RO8 depends on.
- The `RO13` theorem could be strengthened to cover the full `advance` operation
  (i.e., prove that `advance` also preserves Nodup on the output queue) — this would
  allow RO8 to be applied inductively after a sequence of `advance` calls.

---

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24756643900)
> automated formal verification. Current state: **49 files, 511 theorems, 0 sorry**.
> Run 74: Task 5 (Proof Assistance — Progress.lean PR31–PR35, 5 new theorems proved) +
> Task 7 (Critique update — Progress correspondence tests, 0 sorry maintained).

## Run 74 Critique Update

### Task 5: Progress.lean — PR31–PR35 Proved

Run 74 added **5 new theorems** to `Progress.lean` covering the non-Replicate
paths through `maybeDecrTo` and the `optimisticUpdate` function:

- **PR31** (`maybeDecrTo_non_replicate_stale`): In Probe or Snapshot state, `maybeDecrTo`
  with a stale rejected index (i.e., `next_idx ≠ rejected + 1`) returns `(p, false)`.
  Proof: `simp [Progress.maybeDecrTo]` after case-splitting on state and decidability
  of `next_idx == rejected + 1`.

- **PR32** (`maybeDecrTo_non_replicate_decr`): In Probe or Snapshot state, a fresh
  rejected index triggers the decrement path: `next_idx` is set to
  `max (min rejected (match_hint + 1)) (matched + 1)`.  This captures the
  "probe step-back" semantics precisely.

- **PR33** (`maybeDecrTo_preserves_wf`): `maybeDecrTo` preserves the `Progress.wf`
  invariant (`matched + 1 ≤ next_idx`) in all states.  The key insight for the
  non-Replicate case is `Nat.le_max_right : n ≤ max m n`, ensuring the floor
  `matched + 1` is always respected.

- **PR34** (`optimisticUpdate_semantics`): `optimisticUpdate n p` sets `next_idx := n + 1`
  (the optimistic advance for a pipeline-sent entry).

- **PR35** (`optimisticUpdate_preserves_wf`): `optimisticUpdate n p` preserves
  `Progress.wf` when `n ≥ p.matched` — i.e., the optimistic advance does not
  retract the `next_idx` below `matched + 1`.

A private helper `beq_replicate_false_of_ne` was added to prove `(p.state == Replicate) = false`
given `h : p.state ≠ Replicate`.  The key lemma was `beq_eq_false_iff_ne.mpr h`
(Lean 4 core lemma for `LawfulBEq` types, avoiding brittle `cases`-on-field-access patterns).

### Task 7: ProgressCorrespondence.lean — 46 Runtime Tests

`FVSquad/ProgressCorrespondence.lean` was created with **46 `#guard` tests** covering:
- `maybeUpdate` forward-progress and no-op paths
- `maybeDecrTo` in Replicate, Probe, and Snapshot states (stale and fresh paths)
- `optimisticUpdate` pessimistic advance
- `becomeProbe`, `becomeReplicate`, `becomeSnapshot` state transitions

All `#guard` tests pass at compile time via `lake build`, confirming the Lean model
produces the expected output on representative inputs.

**Invariant checks**: `wf` preservation is tested using
`checkWf p := Nat.ble (p.matched + 1) p.next_idx` rather than `decide (p.wf ...)`,
because `Progress.wf` is not marked `@[reducible]` and instance synthesis cannot
unfold it during `decide` elaboration in `#guard` without `@[reducible]`.

**Correspondence level**: *abstraction* — the Lean `Progress` model replaces the
Rust `Inflights` ring buffer with a single `ins_full : Bool` flag.  All `maybeDecrTo`
and `maybeUpdate` paths are faithfully covered; `Inflights` logic is out of scope.

### Project Assessment: 0 Sorry Maintained

Run 74 adds 5 proved theorems and 1 new correspondence file while maintaining
0 sorry across all 49 Lean files and 511 theorems.

**High-value additions**:
- PR33 (wf preservation via `maybeDecrTo`) is the most significant: it closes the
  invariant-preservation gap for all non-Replicate states that prior runs left unproved.
- PR35 (wf preservation via `optimisticUpdate`) is similarly important for the
  pipeline-optimistic path.

**Recommendations for future runs**:
1. **Progress ↔ Raft integration**: The `Progress` invariants (PR1–PR35) form a
   strong foundation.  The next high-value target is proving that the broader
   `raft-rs` state-machine loop maintains `Progress.wf` for all tracked peers —
   this would require formalising the enclosing `ProgressTracker` update loop.
2. **Inflights correspondence**: The `ins_full` abstraction for `Inflights` has not
   been validated against the ring-buffer implementation.  A correspondence test
   harness (Route B) comparing `Inflights` behaviour against the Boolean abstraction
   would increase confidence in results that depend on `maybeReset` and `freeTo`.
3. **Lean 4 `@[reducible]`**: Adding `@[reducible]` to `Progress.wf` would allow
   `decide` to synthesise `Decidable (p.wf)` without expanding manually, simplifying
   future correspondence tests.

---

> 🔬 Updated by [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24760390415)
> automated formal verification. Current state: **50 files, 569 theorem declarations, 0 sorry**.
> Run 76: Task 7 (Proof Utility Critique — MaybePersist.lean 13T section added,
> ProgressCorrespondence 55 #guard section, counts updated 511→569).

## Run 76 Critique Update

### Task 4/Task 7: MaybePersist.lean — Async-Persist Safety Guards

Run 75 added `MaybePersist.lean` with **13 theorems** (MP1–MP8 + SP1–SP4 + `compose_monotone`),
all proved, 0 sorry, covering two Rust functions from `src/raft_log.rs`:

- **`maybe_persist(index, term)`** (MP1–MP8): Advances the `persisted` index only when three
  guards hold: `index > persisted`, `index < firstUpdateIndex`, and `logTerm(index) = term`.
  The three guards prevent: regression (MP5), overtaking uncommitted unstable entries (MP6),
  and stale-term entries from a previous leadership epoch (MP7).

- **`maybe_persist_snap(index)`** (SP1–SP4): Simpler snapshot-persist variant — advances
  `persisted` iff `index > persisted`.

**Proof strategy**: All 13 theorems proved by `by_cases` + `simp` + `omega` with no helper
lemmas. The guards are encoded as a conjunction, so `by_cases` on the conjunction splits
exactly into the `true` and `false` paths.

#### Assessment of MaybePersist proofs

| Theorem | Level | Bug-catching potential | Notes |
|---------|-------|----------------------|-------|
| `maybePersist_true_iff` (MP1) | Mid | **High** | Precisely states all three guards; would catch any guard removal or reordering |
| `maybePersist_monotone` (MP2) | Low | **High** | Persisted never regresses; catches monotonicity violations in the async path |
| `maybePersist_true_advances` (MP3) | Low | Medium | New persisted = index; confirms exact semantics |
| `maybePersist_false_unchanged` (MP4) | Low | Medium | Guards-fail path: persisted unchanged |
| `maybePersist_true_gt` (MP5) | Mid | **High** | Strict monotonicity; would catch `≥` vs `>` guard bugs |
| `maybePersist_true_lt_fui` (MP6) | Mid | **High** | Persisted stays below firstUpdateIndex; critical async correctness property |
| `maybePersist_true_term` (MP7) | Mid | **High** | Term guard integrity; would catch term-mismatch bugs after leadership change |
| `maybePersist_idempotent` (MP8) | Mid | **High** | Re-applying same args returns false; guards against double-advance race |
| `maybePersistSnap_true_iff` (SP1) | Low | Medium | Simpler snap path; exact iff characterisation |
| `maybePersistSnap_monotone` (SP2) | Low | **High** | Snap persisted never regresses |
| `maybePersistSnap_true_advances` (SP3) | Low | Low | Exact new value |
| `maybePersistSnap_false_unchanged` (SP4) | Low | Low | No-change path |
| `compose_monotone` | Low | Medium | Chained persist+snap-persist: global monotonicity preserved |

**Overall assessment**: The MaybePersist proofs are **high-utility**. The three-guard structure
of `maybe_persist` is subtle — it encodes Raft's async-persist safety contract, which is critical
for systems that asynchronously flush log entries to stable storage. Theorems MP5 (strict
monotonicity), MP6 (below firstUpdateIndex), and MP7 (term guard) directly formalise the
three correctness obligations that prevent data loss or illegal advancement of the persisted
pointer under concurrent leadership changes.

**Known gap (CLOSED — Run 92)**: ~~The Lean model abstracts `firstUpdateIndex` as a bare `Nat` parameter.~~
`UnstablePersistBridge.lean` (Run 92) closes this gap: it models the full derivation of
`firstUpdateIndex` from `Unstable.wf` and proves (UPB8) that when `wf u` holds, any successful
advance by `maybePersistFui` produces `newPersisted < u.offset`. The end-to-end safety chain
from `LogUnstable.wf` through `MaybePersistFUI` is now formally verified (0 sorry).

**Remaining concern**: The `Unstable.wf` invariant itself (`snap.idx < offset`) must be
maintained by all callers of `restore` and `stableEntries`. This is not yet proved inductively
for the full Raft state machine — but UPB8 makes the safety of `maybe_persist` conditional on
`wf`, which is a well-defined and checkable precondition.

### Task 7 (continued): ProgressCorrespondence — 55 Runtime Tests

`FVSquad/ProgressCorrespondence.lean` (Run 71/74) contains **55 `#guard` tests** covering:

- `maybeUpdate`: forward-progress path (sets `matched` + optimistic `next_idx`) and no-op
  path (stale index ignored)
- `maybeDecrTo` in **Replicate** state: stale path (not `next_idx-1`) and fresh path
  (step-back to `max(rejected, matched+1)`)
- `maybeDecrTo` in **Probe** state: stale and fresh paths (probe step-back semantics)
- `maybeDecrTo` in **Snapshot** state: similar
- `optimisticUpdate`: pessimistic advance (`next_idx := n + 1`)
- State transitions: `becomeProbe`, `becomeReplicate`, `becomeSnapshot`
- Invariant checks via `checkWf` (monotonicity guard: `matched + 1 ≤ next_idx`)

All 55 `#guard` tests pass at compile time via `lake build`.

**Correspondence level**: *abstraction* — `Inflights` ring buffer replaced by `ins_full : Bool`.

### Project-Wide Statistics (Run 92)

| Metric | Run 76 | Run 92 |
|--------|--------|--------|
| Total theorem declarations | 569 | **544**† |
| Lean 4 files | 50 | **58** (39 proof + 19 correspondence) |
| `sorry` remaining | 0 | **0** ✅ |
| `#guard` tests | 304 | **412** |
| Rust correspondence tests | 13 | **19** |
| Lean 4 version | 4.28.0 | 4.28.0 |

†Theorem count corrected from 575 (stale inflated count) to 544 via Python scan of actual `^theorem` declarations (536 pre-Run 92 + 8 UPB theorems).

**Recommendations for future runs**:

1. **Progress ↔ ProgressTracker integration**: Prove that the per-peer `Progress` invariant
   is preserved by the enclosing `ProgressTracker` update loop. This would leverage PR1–PR35
   and lift correctness to the multi-peer level.

2. **`Unstable.wf` inductive preservation**: Prove that all callers of `restore` and
   `stableEntries` preserve `Unstable.wf`. This would make the UPB8 safety result unconditional
   across the full Raft state machine.

3. **Election model gap (A1–A5)**: See Active/Future Targets section in TARGETS.md — the
   `RaftReachable.step` hypotheses remain abstract axioms. Closing this gap requires
   `RaftElection.lean` and `ConcreteRaft.lean`.

4. **Recompile paper.pdf**: The conference paper needs a fresh `latexmk` run with updated
   statistics (544T/58F/412 `#guard`/19 correspondence targets).

> 🔬 Run 92 statistics update (2026-04-24 04:11 UTC). [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24871315223)

---

## Run 105 Critique Update (2026-04-25)

### Project Statistics (Runs 93-105)

| Metric | Run 92 | Run 105 |
|--------|--------|---------|
| Total theorem declarations | 544 | **628** (+84) |
| Lean 4 files | 58 | **65** (+7 proof files) |
| `sorry` remaining | 0 | **0** |
| `#guard` tests (correspondence) | 412 | **450+** |
| Lean 4 version | 4.28.0 | 4.30.0-rc2 |

### New Layers Added Since Run 92

#### Layer 10: `RaftElection.lean` — 53 theorems (RE1-RE53)

The most substantial single-file addition since the last critique.  Formalises the full election
model: `NodeRole`, `NodeState`, `VoteRecord`, `wonInTerm`, `voteGranted`.

- **`electionSafety` (RE5)**: at most one leader per term — proved from quorum intersection (HQ20) plus the single-valued `VoteRecord` function.
- **RV1-RV8**: complete biconditionals for `voteGranted` — the exact vote-granting condition from Raft §5.4.1 as implemented in `src/raft.rs`.
- Max-term theorem: elected leaders have the highest observed term.
- Role-unchanged: `processVoteRequest` preserves role unless a vote is granted.

Verified against Rust source via `ElectionCorrespondence.lean` (23 `#guard` tests, all pass).

**Assessment**: Very high value. RE5 is the fundamental Raft election safety property proved
directly from quorum intersection. RV1-RV8 give a machine-checked, complete specification of
the vote-granting predicate.

#### Layer 11: `JointTally.lean` (14T) + `JointSafetyComposition.lean` (10T)

Closes the joint-quorum safety proof. JSC1-JSC10 prove that `jointCommittedIndex` is:
- bounded above by both sub-quorum committed indices (safety)
- maximal (no larger index has majority support from both groups)
- monotone (acks can only advance)

Together with the existing `JointCommittedIndex.lean` (JCI1-JCI10), the full joint-config Raft
safety guarantee is now formally established — this covers the Raft membership-change safety
property, one of the two subtlest parts of the protocol.

#### Layer 12: `MultiStepReachability.lean` — 7 theorems (MS1-MS7)

`listStep_safe` (MS2) is the **complete N-step end-to-end safety certificate**: any cluster
reachable by a finite sequence of well-formed AppendEntries steps is state-machine safe.

```
listStep_safe (MS2)
  uses raftReachable_safe (RT2, RaftTrace)
  uses listStep_raftReachable (MS1)
    uses validAEStep_raftReachable (CPS2) at each step
```

Closes the multi-step generalisation gap noted in prior critiques.  **High value**: provides
the final inductive certificate that safety is preserved over all reachable states, not just
single-step transitions.

#### Layer 13: `ProgressTracker.lean` — 24 theorems (PT1-PT24)

PT16-PT24 added since Run 76.  Highlights:
- **PT22**: `hasPeer (initTracker ids ni) id = true <-> id in ids` — exact membership of freshly initialised tracker
- **PT23**: complement of PT22
- **PT24**: `applyChanges` does not change membership for peers absent from the change list

PT22 pins the semantics of `initTracker` (models `ProgressTracker::new`); PT24 is the key
stability property: configuration changes only affect peers appearing in the change list.

#### Layer 14: `ConfigurationInvariants.lean` — 11 theorems (CI1-CI12)

Formalises `VotersLearnersDisjoint` and proves it for all key constructors.

**Key finding (CI9-CI12)**: The initially stated 4-clause predicate is *stricter* than the Rust
demotion state, which allows `outgoing n learners_next != empty`.  The strict predicate
incorrectly rejects valid Raft cluster states during peer demotion.  CI11 exhibits this as a
`#guard`-verified counterexample.  The relaxed 3-clause predicate (`VotersLearnersDisjointRelaxed`)
matches the actual Rust semantics and is proved by CI12 to be satisfied by `mkConfiguration`.

This is a **genuine finding**: proofs relying on the strict predicate are overly conservative.

#### Layer 15: `ReadOnly.lean` — 13 theorems (RO1-RO13), 0 sorry

Previously noted as 12T/1 sorry.  RO8 was proved in Run 64; RO13 (`addRequest_preserves_nodup`)
added subsequently.  All 13 ReadOnly theorems proved, 0 sorry.

### Gaps and Recommendations (Run 105)

1. **LeaderCompleteness full chain**: `HLogConsistency` is still taken as a hypothesis via the
   ER2 chain. Connecting `ElectionBroadcastChain.lean` to the concrete `RaftReachable` trace
   to discharge `HLogConsistency` unconditionally is the **single highest-priority remaining gap**.

2. **VotersLearnersDisjointRelaxed propagation**: Any proof using the strict predicate should
   be reviewed. Update `CORRESPONDENCE.md` to note which proofs depend on the strict form.

3. **Term-indexed safety**: The current `isClusterSafe` model is index-only. Connecting
   `MaybeCommit.lean`'s MC4 (committed advances only to current-term entries) to the top-level
   safety proof would formalise Raft §5.4.2 more closely.

4. **ProgressTracker integration**: Prove that a reachable Raft state's progress map always
   satisfies `all_wf`. PT1-PT24 prove per-operation invariants but there is no integration
   theorem connecting to `RaftReachable`.

5. **Paper update**: `paper.tex` needs updated statistics (628T, 65F, 0 sorry, 450+ `#guard`,
   22 correspondence targets, 1 finding: CI9-CI12 demotion finding).

> 🔬 Run 105 critique update (2026-04-25 04:00 UTC). [Lean Squad](https://github.com/dsyme/raft-lean-squad/actions/runs/24921939370)
