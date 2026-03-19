commit 19256886d0d6115dba8da4292e7344cc6507d4bf
Author: github-actions[bot] <github-actions[bot]@users.noreply.github.com>
Date:   Thu Mar 19 05:22:41 2026 +0000

    Add JointConfig joint quorum: informal spec, Lean 4 spec + implementation (Tasks 1+2+3+4)
    
    New FV target 7: JointConfig joint quorum (src/quorum/joint.rs).
    
    Task 1 (Research): Added Target 7 to RESEARCH.md and TARGETS.md.
      - Joint quorum: two majority configs, both must agree on commit/vote
      - Key safety property: joint committed index ≤ each individual quorum
      - Vote logic: Won iff both Won; Lost iff either Lost; Pending otherwise
    
    Task 2 (Informal Spec): specs/joint_quorum_informal.md
      - vote_result: preconditions, postconditions, edge cases, examples
      - committed_index: safety invariant, monotonicity, empty-config handling
      - Open questions: use_group_commit flag, overlapping membership
    
    Tasks 3+4 (Lean Spec + Implementation): FVSquad/JointQuorum.lean (0 sorry)
      - JointConfig structure (two Finset Nat)
      - jointVoteResult: exact translation of joint.rs vote_result match
      - jointCommittedIndex: min(i_idx, o_idx)
      - 20+ theorems proved (0 sorry):
        * jointVoteResult_won_iff: Won ↔ incoming=Won ∧ outgoing=Won
        * jointVoteResult_lost_iff: Lost ↔ incoming=Lost ∨ outgoing=Lost
        * jointVoteResult_pending_iff: characterises Pending
        * jointVoteResult_empty_outgoing/incoming: simplification to single quorum
        * jointVoteResult_won/lost_of_incoming/outgoing: monotone lifting
        * jointVoteResult_not_lost_incoming/outgoing: safety corollaries
        * jointCommittedIndex_le_left/right: safety (joint ≤ each quorum)
        * jointCommittedIndex_mono_left/right: monotonicity
        * jointCommittedIndex_comm, eq_min, eq_left/right: min properties
        * jointCommittedIndex_safety: joint is strictly finer than each quorum
        * jointVoteResult_won_implies_each: Won forces both sub-quorums Won
    
    Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>

diff --git a/formal-verification/specs/joint_quorum_informal.md b/formal-verification/specs/joint_quorum_informal.md
new file mode 100644
index 0000000..667853e
--- /dev/null
+++ b/formal-verification/specs/joint_quorum_informal.md
@@ -0,0 +1,144 @@
+# Informal Specification — `JointConfig` Joint Quorum
+
+> 🔬 *Lean Squad — informal specification for FV target.*
+
+**Source**: `src/quorum/joint.rs`  
+**FV Target**: Task 2 — Informal Spec Extraction
+
+---
+
+## Purpose
+
+`JointConfig` represents a Raft cluster configuration *during* a membership change.
+It contains two `MajorityConfig`s (incoming and outgoing). Under *joint consensus*,
+any decision — a commit or a vote — requires the agreement of *both* constituent
+majorities, not just one.
+
+This is the mechanism that prevents split-brain during reconfiguration: until the
+old cluster has been fully removed, it still has a veto.
+
+---
+
+## Structure
+
+```rust
+pub struct Configuration {
+    pub(crate) incoming: MajorityConfig,   // new voter set
+    pub(crate) outgoing: MajorityConfig,   // old voter set (empty in normal operation)
+}
+```
+
+In normal operation (no membership change in progress), `outgoing` is empty and the
+configuration degrades to a simple majority.
+
+---
+
+## `vote_result` Operation
+
+### Purpose
+Determine the outcome of a vote (election or pre-vote) given the current votes.
+
+### Logic
+```rust
+fn vote_result(check: impl Fn(u64) -> Option<bool>) -> VoteResult {
+    let i = incoming.vote_result(&check);
+    let o = outgoing.vote_result(check);
+    match (i, o) {
+        (Won, Won) => Won,
+        (Lost, _) | (_, Lost) => Lost,
+        _ => Pending,
+    }
+}
+```
+
+### Preconditions
+- `check` maps voter IDs to `Some(true)` (yes), `Some(false)` (no), or `None` (not yet voted).
+- Voter IDs may appear in both `incoming` and `outgoing` (overlapping membership is valid).
+
+### Postconditions
+- Returns `Won` iff both `incoming.vote_result` = Won **and** `outgoing.vote_result` = Won.
+- Returns `Lost` iff `incoming.vote_result` = Lost **or** `outgoing.vote_result` = Lost.
+- Returns `Pending` in all other cases.
+
+### Invariant: Outcomes are mutually exclusive
+- `Won` and `Lost` cannot both hold simultaneously.
+- `Pending` holds iff neither `Won` nor `Lost`.
+
+### Edge cases
+- **Both empty**: both sub-configs are empty → each returns `Won` (by convention) → joint is `Won`.
+- **Outgoing empty** (normal operation): joint result = incoming result.
+- **Incoming empty** (degenerate): joint result = outgoing result.
+- **Overlapping voters**: a voter in both sets contributes their vote to both sub-quorum computations.
+
+### Inferred intent
+The semantics model a *strict AND* of two independent elections. This is more conservative
+than a simple union: even if `incoming` has won, the result is Pending until `outgoing` also wins.
+This ensures the old cluster retains veto power during transition.
+
+### Examples
+- `incoming={1,2,3}` all vote yes, `outgoing={1,2}` all vote yes → `Won`
+- `incoming={1,2,3}` all vote yes, `outgoing={1,2,3}` voter 3 votes no → `Lost`
+- `incoming={1,2,3}` voter 2 not yet voted, `outgoing={1,2}` both voted yes → `Pending` (incoming not decided)
+
+---
+
+## `committed_index` Operation
+
+### Purpose
+Determine the largest log index that has been committed under the joint quorum.
+
+### Logic
+```rust
+fn committed_index(use_group_commit, l) -> (u64, bool) {
+    let (i_idx, i_gc) = incoming.committed_index(use_group_commit, l);
+    let (o_idx, o_gc) = outgoing.committed_index(use_group_commit, l);
+    (min(i_idx, o_idx), i_gc && o_gc)
+}
+```
+
+### Special case: empty config
+When `incoming` (or `outgoing`) is empty, `MajorityConfig::committed_index` returns
+`(u64::MAX, true)`. Therefore `min(u64::MAX, o_idx) = o_idx` — the empty incoming
+config contributes no constraint, and the joint committed index equals the outgoing index.
+This is the "normal operation" path where `outgoing` is empty → joint committed = incoming committed.
+
+### Postconditions
+- `joint_committed ≤ incoming_committed`
+- `joint_committed ≤ outgoing_committed`
+- `joint_committed = min(incoming_committed, outgoing_committed)`
+
+### Invariant: Joint is stricter than either quorum alone
+The joint committed index is always ≤ each individual committed index. This ensures that
+an entry must be replicated to both quorums before it is considered committed — the key
+Raft safety requirement during reconfiguration.
+
+### Monotonicity
+If `incoming_committed` increases and `outgoing_committed` stays the same (or vice versa),
+`joint_committed` is non-decreasing.
+
+### Edge cases
+- **Both empty**: both return `u64::MAX`, joint committed = `u64::MAX`.
+- **One empty**: acts as identity; joint committed = the other config's committed index.
+- **Both have same committed index**: joint committed = that index.
+
+---
+
+## Open Questions
+
+1. **`use_group_commit`** flag: The group commit optimisation is tracked separately.
+   Should the Lean model capture the `bool` return (group commit flag) or just the `Nat`?
+   Currently deferred — the model verifies only the index, not the flag.
+
+2. **Overlapping membership**: When a voter appears in both `incoming` and `outgoing`,
+   their acked index is counted twice (once for each sub-quorum). Is this intentional?
+   The Rust code does not deduplicate — each call to `vote_result`/`committed_index`
+   evaluates the sub-quorum independently.
+
+3. **Transition to simple majority**: Once the membership change completes, `outgoing`
+   is cleared. At that point `joint.committed_index = incoming.committed_index`.
+   The Lean model should eventually prove this transition is safe (no committed entries
+   can be "uncommitted" when `outgoing` is cleared).
+
+---
+
+*Generated by Lean Squad — FV automation for `dsyme/fv-squad`.*
