# Informal Specification: `maybe_commit_by_vote`

**Source**: `src/raft.rs`, `RaftCore::maybe_commit_by_vote` (lines ≈ 2219–2250)

**Target phase**: 2 — Informal Spec

---

## Purpose

`maybe_commit_by_vote` is a fast-forward optimisation for Raft followers and candidates.
When a node receives a vote *rejection* (either `MsgRequestVoteResponse` with `reject=true`
or a `MsgRequestPreVoteResponse`), the reply carries `commit` and `commit_term` fields
from the rejecting voter. If those fields indicate the cluster has committed entries that
the local node hasn't yet committed, this function advances the local commit index to
match — without waiting for a full `AppendEntries` round trip.

This is a TiKV-specific optimisation layered on top of standard Raft; it does not appear
in the original Raft paper.

---

## Relevant Rust code

```rust
fn maybe_commit_by_vote(&mut self, m: &Message) {
    if m.commit == 0 || m.commit_term == 0 {
        return;
    }
    let last_commit = self.raft_log.committed;
    if m.commit <= last_commit || self.state == StateRole::Leader {
        return;
    }
    if !self.raft_log.maybe_commit(m.commit, m.commit_term) {
        return;
    }
    // ... logging ...
    if self.state != StateRole::Candidate && self.state != StateRole::PreCandidate {
        return;
    }
    // Scan newly committed entries for config changes.
    let low = last_commit + 1;
    let high = self.raft_log.committed + 1;
    let ctx = GetEntriesContext(GetEntriesFor::CommitByVote);
    if self.has_unapplied_conf_changes(low, high, ctx) {
        let term = self.term;
        self.become_follower(term, INVALID_ID);
    }
}
```

---

## Preconditions

- Called only when the node receives a vote *rejection response* (i.e. the rejecting
  voter's committed state is piggy-backed on the message).
- `m.commit` is the rejecting voter's committed index (0 if not set).
- `m.commit_term` is the term of the entry at `m.commit` (0 if not set).
- The local `raft_log.committed` is the node's current commit index.
- The local node state is one of: Follower, Candidate, PreCandidate (not Leader).
  (If Leader, there is an early return.)

---

## Postconditions

1. **Guard: invalid commit fields** — If `m.commit == 0 || m.commit_term == 0`, nothing
   changes: `committed` is unchanged, state is unchanged, returns immediately.

2. **Guard: already caught up or leader** — If `m.commit ≤ raft_log.committed`
   (already committed at least as much) OR `state == Leader`, nothing changes.

3. **Guard: maybe_commit fails** — `RaftLog::maybe_commit(m.commit, m.commit_term)` is
   the normal commit advancement logic; it succeeds only if `m.commit > committed` AND
   `term_of(m.commit) == m.commit_term`. If it fails (e.g., the local log doesn't have
   the entry, or the term doesn't match), nothing further happens.

4. **Commit advancement** — If `maybe_commit` succeeds:
   - `raft_log.committed` is advanced to `m.commit`.
   - The committed index is **monotone**: it never decreases.

5. **Config-change safety for candidates** — If state is Candidate or PreCandidate AND
   the newly-committed entries `(old_commit+1 .. new_commit]` include a config change:
   - The node calls `become_follower(current_term, INVALID_ID)`.
   - This is a defensive measure: config changes during elections are assumed unsafe,
     so the candidate steps down (at the *same* term, not a higher one).

6. **No state change for followers** — If state is Follower (after commit advance), the
   config-change scan is not performed; the node remains a Follower.

---

## Invariants

- **Committed index monotonicity**: This function never decreases `committed`. All
  code paths either leave `committed` unchanged or call `maybe_commit` which is itself
  monotone.
- **Leader exclusion**: A leader never fast-forwards its commit via this path (early
  guard). Leaders commit via the normal quorum tracking path.
- **Candidate step-down only on config change**: Candidates step down *only* if a
  config change is among the newly committed entries. Otherwise they remain candidates.
- **Term preserved on step-down**: `become_follower` is called with `self.term`
  (current term), not a higher term. The term does not change due to this function.

---

## Edge Cases

- **`m.commit == 0`**: Treated as "no commit info" — function returns immediately.
  This is the case when old-format messages (pre-optimisation) are received.
- **Local log doesn't have the entry**: `maybe_commit` checks the log term; if the
  entry at `m.commit` isn't in the local log yet, the commit cannot be advanced.
- **Commit exactly equal to current**: `m.commit <= last_commit` guard prevents
  redundant calls. If equal, returns without doing anything.
- **No config change in committed range**: Candidate stays a candidate; the commit
  advance still occurs. The candidate continues the election with a higher commit index.
- **Multiple calls**: Idempotent in the sense that a second call with the same `m.commit`
  will hit the `m.commit <= last_commit` guard and do nothing.

---

## Candidate Propositions for Lean Spec (Phase 3)

| ID | Property |
|----|----------|
| P1 | `commit_monotone`: `raft_log.committed` only increases |
| P2 | `invalid_fields_noop`: `commit == 0 ∨ commit_term == 0 → no state change` |
| P3 | `already_committed_noop`: `m.commit ≤ committed → no state change` |
| P4 | `leader_noop`: `state == Leader → no state change` |
| P5 | `config_change_causes_stepdown`: if newly committed range has conf change AND was Candidate → state becomes Follower |
| P6 | `no_config_change_stays_candidate`: no conf change in range AND was Candidate → state stays Candidate |
| P7 | `follower_stays_follower`: state was Follower AND commit advances → state remains Follower |
| P8 | `term_preserved_on_stepdown`: `become_follower` called with same term → term unchanged |

---

## Open Questions

1. **What if the local log lacks `m.commit`?**: `maybe_commit` checks
   `term_of(m.commit)` — if the entry isn't locally present, the check fails silently.
   Is there a risk of indefinitely deferring commits that should be applied?
2. **Config-change scan pagination**: `has_unapplied_conf_changes` paginates the scan
   to avoid memory spikes. What is the page size? Could a large committed range cause
   latency?
3. **Follower fast-commit without apply**: The commit index is advanced before
   `apply_to` is called. Is it possible for the application layer to miss entries if
   the process crashes between commit-advance and apply?
4. **Is this optimisation in the canonical TiKV Raft spec?**: The code comment says
   "as we assume quorum won't change during election" — is this invariant formally
   documented anywhere?

---

> 🔬 *Generated by Lean Squad automated formal verification.*
