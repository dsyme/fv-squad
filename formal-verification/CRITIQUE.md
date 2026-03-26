# FV Proof Utility Critique

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Honest assessment of the formal verification work done so far: are the proved properties
meaningful, at the right level of abstraction, and likely to catch real bugs?

## Last Updated
- **Date**: 2026-03-26 23:50 UTC
- **Commit**: `06d920b941a9182a3f6f03d031136fd9dc272c31`

---

## Overall Assessment

Five core Raft sub-functions have been formally specified and fully proved in Lean 4 (0
`sorry` across ~91 theorems on `main`, plus 12 more in a pending PR for
`find_conflict`).  The most safety-critical result is `committedIndex_safety` and
`committedIndex_maximality`, which directly encode Raft's core quorum-acknowledgement
guarantee.  `configValidate_iff_valid` precisely characterises valid configurations and
would catch any added or removed check in `Config::validate`.  The overall proof coverage
is solid for the pure, leaf-level functions; the main gap is that the higher-level
orchestration (`maybe_append`, `joint_committed_index`, leader election) is untouched.
No implementation bugs have been found.

---

## Proved Theorems: Assessment Table

### `formal-verification/lean/FVSquad/LimitSize.lean`
**Target**: `limit_size` — `src/util.rs:54`
**25 theorems, 0 sorry**

| Theorem | Level | Bug-catching | Notes |
|---------|-------|-------------|-------|
| `totalSize_take_le` | Low | Low | Helper: `totalSize (take n l) ≤ totalSize l` |
| `limitSizeCount_*` (8 helpers) | Low | Low | Internal scan correctness lemmas |
| `limitSize_is_prefix` | Mid | Medium | Guarantees the result is a prefix of the input — a truncation cannot reorder |
| `limitSize_nonempty` | Mid | Medium | Non-empty input → non-empty output (no over-truncation to empty) |
| `limitSize_size_bound` | Mid | **High** | Every returned entry fits within the budget — would catch a bug permitting oversized output |
| `limitSize_maximality` | Mid | **High** | No strict prefix also fits — catches an off-by-one in the budget check |
| `limitSize_idempotent` | Mid | Medium | Running `limit_size` twice is the same as once |
| `limitSize_all_fit_noop` | Mid | Medium | If everything fits, nothing is dropped |
| `limitSize_length_le` | Low | Low | Structural size bound |
| `limitSize_prefix_of_prefix` | Mid | Medium | Monotonicity of truncation with respect to budget |

**Assessment**: Most theorems are structural helpers or sanity lemmas.  The two
high-value results are `limitSize_size_bound` and `limitSize_maximality`; together they
provide a tight characterisation of the truncation behaviour.  A bug that included too
many entries or excluded one that fits would be caught.

**Concern**: The `size` function is fully abstract (`α → Nat`).  This means the proofs
hold for *any* size function, which is a strength in terms of generality but means we
have not verified anything about the actual `compute_size()` serialisation computation.

---

### `formal-verification/lean/FVSquad/ConfigValidate.lean`
**Target**: `Config::validate` — `src/config.rs`
**10 theorems, 0 sorry**

| Theorem | Level | Bug-catching | Notes |
|---------|-------|-------------|-------|
| `configValidate_iff_valid` | **High** | **Very High** | Biconditional: `validate = true ↔ all 7 conditions hold` |
| `defaultCfg_valid` | Mid | Medium | Default config is valid — regression guard |
| `zero_id_invalid`, `zero_heartbeat_invalid`, etc. (5 direct) | Mid | High | Each catches removal/weakening of one validation check |
| `valid_inflight_increase` | Mid | Medium | Inflight allowance monotone with max |
| `configValidate_false_iff_invalid` | Mid | Medium | Dual of the biconditional |

**Assessment**: This is the highest-precision specification in the codebase.  The
biconditional `configValidate_iff_valid` precisely captures all seven validation checks.
Any addition, removal, or weakening of a check in the Rust would falsify at least one
theorem.  The specification is tight — it is not possible to satisfy these theorems with
an incorrect implementation.

---

### `formal-verification/lean/FVSquad/MajorityVote.lean`
**Target**: `Configuration::vote_result` — `src/quorum/majority.rs`
**21 theorems, 0 sorry**

| Theorem | Level | Bug-catching | Notes |
|---------|-------|-------------|-------|
| `majority_pos`, `majority_gt_half`, `majority_exceeds_half`, `majority_monotone` | Low | Low | Arithmetic helpers |
| `yesCount_*`, `missingCount_*` (5) | Low-Mid | Low | Count helpers |
| `voteResult_empty_is_Won` | Mid | Medium | Edge case: empty voter set always wins |
| `voteResult_Won_iff` | **High** | **Very High** | Exact characterisation of when a vote wins |
| `voteResult_Lost_iff` | **High** | **Very High** | Exact characterisation of when a vote fails |
| `voteResult_Pending_iff` | **High** | **High** | Characterisation of the undecided case |
| `single_yes_wins` | Mid | Medium | Degenerate 1-voter case |
| `voteResult_majority_yes_wins` | Mid | **High** | Explicitly: majority yes → Won; catches majority calculation bugs |
| `voteResult_not_Won_of_few_yes` | Mid | **High** | Below majority → not Won; catches over-counting bugs |
| `voteResult_all_yes` | Mid | Medium | All yes → Won |
| `voteResult_exhaustive` | Mid | Medium | Exactly one of Won/Lost/Pending always holds |

**Assessment**: Strong coverage.  The biconditionals for Won, Lost, and Pending are
tight.  A bug that miscounted yes/no votes, used the wrong majority threshold, or
confused Won/Pending would be caught.

**Main concern**: Voter lists use `List Nat` instead of `Finset Nat` (a deduplicated
set).  In practice, Raft uses `HashSet<u64>` voters.  A list with duplicate voter IDs
could inflate `yesCount`, breaking the majority guarantee.  The model is correct *under
the assumption* that the input list has no duplicates, but this is not formally
enforced.  This is noted in CORRESPONDENCE.md.

---

### `formal-verification/lean/FVSquad/JointVote.lean`
**Target**: `JointConfig::vote_result` — `src/quorum/joint.rs`
**14 theorems, 0 sorry**

| Theorem | Level | Bug-catching | Notes |
|---------|-------|-------------|-------|
| `combineVotes_Won_iff`, `combineVotes_Lost_iff`, `combineVotes_Pending_iff`, `combineVotes_symm_Lost` | Mid | High | Combinatorial logic for two vote results |
| `jointVoteResult_Won_iff` | **High** | **Very High** | Won requires Won in *both* configs |
| `jointVoteResult_Lost_iff` | **High** | **Very High** | Lost requires Lost in *at least one* config |
| `jointVoteResult_Pending_iff` | **High** | **High** | Undecided otherwise |
| `jointVoteResult_non_joint` | **High** | **High** | Joint with one empty config = single config result |
| `jointVoteResult_incoming_Lost`, `jointVoteResult_outgoing_Lost` | Mid | **High** | Either config losing kills the joint result |
| `jointVoteResult_all_yes` | Mid | Medium | All yes in both → Won |
| `jointVoteResult_exhaustive` | Mid | Medium | Exactly one of Won/Lost/Pending |
| `jointVoteResult_Won_symm`, `jointVoteResult_Lost_symm` | Mid | Medium | Order of configs does not matter |

**Assessment**: Very strong coverage.  The biconditionals for the joint quorum are
especially valuable: any bug that allows a joint vote to be Won when only one config
agrees would directly falsify `jointVoteResult_Won_iff`.  The symmetry theorems are
a bonus.

**Gap**: The theorems do not yet connect the joint vote result to the safety argument
that *joint commitment requires agreement in both old and new configurations*.  A
higher-level theorem relating joint vote to the Raft joint-consensus safety guarantee
(no two logs can be committed simultaneously) would be the natural next step.

---

### `formal-verification/lean/FVSquad/CommittedIndex.lean`
**Target**: `Configuration::committed_index` — `src/quorum/majority.rs`
**28 theorems (including helpers), 0 sorry**

| Theorem | Level | Bug-catching | Notes |
|---------|-------|-------------|-------|
| `sortDesc_*` (5 helpers) | Low | Low | Sort correctness helpers |
| `countGe_*` (8 helpers) | Low-Mid | Low-Mid | Count-above-threshold helpers |
| `committedIndex_empty` | Mid | Medium | Empty voter set → 0 (Rust: `u64::MAX` — divergence noted) |
| `committedIndex_singleton` | Mid | Medium | Single voter → that voter's acked index |
| `committedIndex_all_zero` | Mid | Medium | All acked=0 → 0 |
| `committedIndex_safety` | **Very High** | **Very High** | The committed index is ≥-acknowledged by ≥ majority of voters |
| `committedIndex_maximality` | **Very High** | **Very High** | No strictly larger index is majority-acknowledged |
| `committedIndex_mono` | **High** | **High** | Monotone: increasing any acked value never decreases the result |

**Assessment**: The crown jewel of the FV suite.  `committedIndex_safety` and
`committedIndex_maximality` together prove Raft's core quorum-acknowledgement correctness
property — this is one of the most important correctness invariants in the entire Raft
protocol.  A bug in the sort-based selection (e.g., ascending instead of descending sort,
wrong majority index) would directly falsify these theorems.

`committedIndex_mono` is also important: it proves that the commit point can only advance
forward, never regress, as followers report higher acked indices.

**Concerns**:
1. *List vs Set*: same voter-duplication concern as `MajorityVote` (see above).
2. *Empty-config divergence*: the model returns 0 for empty configs; Rust returns
   `u64::MAX`.  The theorem `committedIndex_empty_contract` documents this, but proofs
   about joint configs that take `min(a, b)` may need to account for it.
3. *Non-group-commit path only*: the `use_group_commit = true` branch is unmodelled.

---

### `formal-verification/lean/FVSquad/FindConflict.lean` (PR pending)
**Target**: `RaftLog::find_conflict` — `src/raft_log.rs:200`
**12 theorems, 0 sorry**

| Theorem | Level | Bug-catching | Notes |
|---------|-------|-------------|-------|
| `findConflict_empty`, `findConflict_head_mismatch`, `findConflict_head_match` | Low | Low | Structural lemmas |
| `findConflict_zero_of_all_match` | Mid | High | All match → 0; catches spurious conflict reports |
| `findConflict_all_match_of_zero` | Mid | High | 0 → all match; catches missed conflict detection |
| `findConflict_nonzero_witness` | Mid | **High** | Non-zero → specific mismatching entry exists |
| `findConflict_first_mismatch` | **High** | **Very High** | Full characterisation: result = first mismatching entry's index |
| `findConflict_skip_match_prefix` | Mid | **High** | Matching prefix does not affect result |
| `findConflict_singleton_*` | Low | Low | Singleton corollaries |
| `findConflict_zero_iff_all_match` | Mid | **High** | Biconditional (positive-index precondition) |
| `findConflict_result_in_indices` | Low-Mid | Low | Result is always an entry index or 0 |

**Assessment**: Solid structural verification.  `findConflict_first_mismatch` (FC7) is
the most valuable: it proves the function returns the *first* mismatch, not just any
mismatch.  A bug that scanned from the wrong end, skipped entries, or returned a later
mismatch would be caught.  `findConflict_zero_iff_all_match` (FC11) provides the
biconditional that makes the 0 sentinel trustworthy.

---

## Gaps and Recommendations

Prioritised by impact on Raft correctness.

### 1. `joint_committed_index` (Priority: **Very High**)

**What it is**: `JointConfig::committed_index` (`src/quorum/joint.rs`) — the Raft
committed index under joint consensus.  It calls `min(c1.committed_index(acked),
c2.committed_index(acked))` and returns `u64::MAX` if either config is empty.

**Why it matters**: This is the primary safety mechanism during Raft membership changes.
Taking the minimum of the two committed indices ensures no entry is committed unless it
is acknowledged by a majority in *both* the old and new configurations.  A bug here
(e.g., using `max` instead of `min`, or returning the wrong value for an empty config)
could cause a committed log entry to be overwritten during a configuration change.

**Expected effort**: Small — builds directly on `CommittedIndex.lean`.  Key theorem:
`jointCommittedIndex_le_both : jointCommittedIndex cfg acked ≤ committedIndex cfg.outgoing acked ∧ jointCommittedIndex cfg acked ≤ committedIndex cfg.incoming acked`.

**Proof difficulty**: Low — follows from `Nat.min_le_left` and `Nat.min_le_right`.

---

### 2. `maybe_append` (Priority: **High**)

**What it is**: `RaftLog::maybe_append` (`src/raft_log.rs:267`) — calls `find_conflict`
and then decides whether and where to truncate + append the provided entries.

**Why it matters**: Connects `find_conflict` to the actual log mutation.  Key
properties: if `find_conflict` returns 0, the log already contains all provided entries
(no truncation); if non-zero, the log is truncated at the conflict index and the new
entries are appended.

**Expected effort**: Medium — needs to model the log mutation.

---

### 3. Voter deduplication invariant (Priority: **High**)

**What it is**: Formally prove that the `List Nat` voter lists fed into `voteResult` and
`committedIndex` are always duplicate-free.

**Why it matters**: The voter-duplication concern is a semantic gap shared by both
`MajorityVote.lean` and `CommittedIndex.lean`.  If duplicates could appear, the majority
count would be inflated and `committedIndex_safety` would be vacuous for the affected
configurations.  Proving a `Nodup` invariant on the voter lists would close this gap.

**Expected effort**: Medium — requires tracing where voter lists are constructed in the
Rust and adding a `List.Nodup` precondition to the affected theorems.

---

### 4. `inflights` ring buffer (Priority: **Medium**)

**What it is**: `Inflights` in `src/tracker/inflights.rs` — a ring buffer tracking
in-flight messages to followers.

**Why it matters**: Ring buffer invariants are subtle (wrap-around arithmetic).  A bug
in the wrap-around logic could cause messages to be double-counted or missed.

**Expected effort**: Large — ring buffer invariants require careful modelling of the
index arithmetic.

---

### 5. Joint safety theorem (Priority: **Medium**)

**What it is**: A top-level theorem relating `jointCommittedIndex` to Raft's joint
consensus safety argument: under joint configuration, a log entry can only be committed
if it is majority-acknowledged in both old and new configurations.

**Why it matters**: This would close the loop from individual quorum proofs to a
protocol-level safety statement.  It is the strongest claim the current proof suite
could support.

**Expected effort**: Medium — builds on `CommittedIndex.lean` + `JointVote.lean`.

---

## Concerns About Current Proofs

| Concern | Affected theorems | Severity | Action |
|---------|------------------|----------|--------|
| Voter `List` vs `Finset` | `committedIndex_safety`, `voteResult_Won_iff`, `jointVoteResult_Won_iff` | Medium | Proofs hold under `Nodup` assumption — add it as explicit precondition |
| Empty-config value divergence (0 vs `u64::MAX`) | `committedIndex_empty` | Low | Documented; only matters when combining with joint quorum; see `committedIndex_empty_contract` |
| Abstract `size` in `LimitSize` | All `limitSize_*` | Low | Too general to catch `compute_size()` bugs — acceptable as the size function is injected |
| No model of log state transitions | `findConflict_*` | Medium | FC7 proves static properties of the scan; no proof that `maybe_append` uses it correctly |

None of these concerns invalidate existing proofs — they are all correctly stated
relative to their models.  The voter-deduplication concern is the most consequential
because it affects the key safety theorems.

---

## Positive Findings

- **No bugs found** across all verified targets.  The implementations are correct with
  respect to their specifications as modelled.
- `committedIndex_safety` + `committedIndex_maximality`: together these prove Raft's
  quorum acknowledgement correctness.  Finding these hold with 0 `sorry` provides real
  confidence in the committed-index computation.
- `configValidate_iff_valid`: the biconditional is tight — 7 conditions, precisely
  specified.  The default configuration being provably valid is a concrete sanity check.
- `jointVoteResult_Won_iff` requiring Won in *both* sub-configs: directly encodes the
  joint consensus quorum requirement.  Any weakening of this in the Rust would be caught.
