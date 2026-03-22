# Informal Specification: Vote Commitment (at-most-one-vote-per-term)

**Source**: `src/raft.rs` — `step()` (lines ~1487–1515), `reset()` (lines ~1008–1011),
`become_candidate()` (lines ~1176–1192).

---

## Purpose

A core Raft safety invariant: a node may cast **at most one real vote per term**.
This ensures that in any given term, at most one candidate can receive a majority quorum,
which is a prerequisite for the Raft Election Safety property (at most one leader per term).

---

## Preconditions

- A vote request arrives: `MsgRequestVote` from candidate `m.from` in term `m.term`.
- The node may have an existing vote record (`self.vote`) from an earlier request in the same term.

---

## Postconditions

After processing a real vote grant:
- `self.vote = m.from`
- No other vote request in the same term will be granted (unless from the same `m.from`)

---

## The `can_vote` condition (simplified)

```rust
let can_vote =
    (self.vote == m.from)  ||                              // repeat for same candidate
    (self.vote == INVALID_ID && self.leader_id == INVALID_ID); // haven't voted yet
    // (PreVote: m.type == MsgRequestPreVote && m.term > self.term — excluded here)
```

A real vote is recorded only when `can_vote && log_is_up_to_date && priority_ok`:
```rust
self.vote = m.from;   // only for MsgRequestVote, not MsgRequestPreVote
```

---

## Term-change invariant

When the term changes (via `reset(new_term)`):
```rust
if self.term != term {
    self.term = term;
    self.vote = INVALID_ID;   // clear vote on any term change
}
```
After a term change, the node may vote again in the new term.

---

## Invariants

1. **At most one vote per term**: if `vote ≠ INVALID_ID`, the only candidate that
   passes `can_vote` is `vote` itself (repeat-vote branch).
2. **Vote cleared on term change**: `reset(t)` with `t ≠ self.term` always sets
   `vote = INVALID_ID` before any new vote is granted.
3. **Become-candidate: self-vote**: `become_candidate()` increments the term via
   `reset(term+1)` (clearing any existing vote) then sets `vote = id` (self-vote).
4. **Pre-vote does not record a vote**: `MsgRequestPreVote` does NOT update `self.vote`.

---

## Edge cases

- `INVALID_ID = 0`: node ID 0 is reserved; no real node has ID 0.
- A repeat vote request from the same candidate is always granted (idempotence).
- If the node receives a vote request from a higher term, it first resets
  (`vote = INVALID_ID`) then evaluates `can_vote` — so it may grant the new vote.
- `become_candidate()` for a node with an existing vote: `reset(term+1)` clears it.
- `leader_id` check: the production code also requires `self.leader_id == INVALID_ID`
  to grant a first-time vote; our formal model omits this (making the model more
  permissive, which makes safety proofs stronger).

---

## Examples

| State `(term, vote)` | Request `(from, term)` | `can_vote`? |
|----------------------|------------------------|-------------|
| `(3, 0)` | `(5, 3)` | ✓ — no vote yet |
| `(3, 5)` | `(5, 3)` | ✓ — repeat vote |
| `(3, 5)` | `(3, 3)` | ✗ — already voted for 5 |
| `(3, 5)` reset to `(4, 0)` | `(3, 4)` | ✓ — new term clears old vote |

---

## Inferred intent

The invariant is a building block for the Raft Election Safety theorem:
> At most one leader can be elected in any given term.

Because each node grants at most one vote per term, and a leader requires a majority,
two leaders cannot be simultaneously elected in the same term.

---

## Open questions

1. Is the `leader_id == INVALID_ID` check in `can_vote` semantically important for
   the safety invariant, or only an optimisation? (Our model omits it and still proves safety.)
2. Does `become_pre_candidate()` guarantee `vote` is unchanged? The code comment says
   "doesn't change ... self.vote" — should this be verified?

---

🔬 *Lean Squad — informal specification for `vote_commitment`.*
