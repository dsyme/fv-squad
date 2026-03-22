# Informal Spec: `is_local_msg`, `is_response_msg`, `vote_resp_msg_type`

> Source: `src/raw_node.rs` (lines 62–83), `src/raft.rs` (lines 311–320)
> Lean file: `formal-verification/lean/FVSquad/MsgType.lean`
> Phase: 5 — Proofs (all 13 theorems proved by `decide`)

---

## Purpose

Three pure message-type classification functions that drive the raft message
routing and vote-collection logic:

| Function | Source | Returns |
|---|---|---|
| `is_local_msg(t)` | `raw_node.rs` | `true` iff `t` is generated internally (not sent on the wire) |
| `is_response_msg(t)` | `raw_node.rs` | `true` iff `t` is a peer reply |
| `vote_resp_msg_type(t)` | `raft.rs` | The response type for a vote-request type |

---

## Preconditions

- `is_local_msg`, `is_response_msg`: take any `MessageType` value (total functions).
- `vote_resp_msg_type`: in Rust, panics on non-vote inputs. The Lean model returns
  `Option MsgType` (`none` for non-vote types) to avoid partiality.

---

## Postconditions

### `is_local_msg(t) = true`
Exactly when `t ∈ {MsgHup, MsgBeat, MsgUnreachable, MsgSnapStatus, MsgCheckQuorum}`.
These 5 types are never sent over the network.

### `is_response_msg(t) = true`
Exactly when `t ∈ {MsgAppendResponse, MsgRequestVoteResponse, MsgHeartbeatResponse,
MsgUnreachable, MsgRequestPreVoteResponse}`.
These 5 types are replies from peer nodes.

### `vote_resp_msg_type(t)`
- `MsgRequestVote    → MsgRequestVoteResponse`
- `MsgRequestPreVote → MsgRequestPreVoteResponse`
- All other types    → `none` (panic in Rust)

---

## Invariants

- The overlap `{local} ∩ {response} = {MsgUnreachable}` (exactly one type in both sets).
  **This is intentional**: `MsgUnreachable` is triggered locally by the transport
  layer but also handled as a pseudo-response that advances the leader's replication
  pipeline.
- `|{local}| = 5`, `|{response}| = 5`.
- The 10 remaining types are "request/outbound" messages (neither local nor response).
- `vote_resp_msg_type` is injective on `{MsgRequestVote, MsgRequestPreVote}`.
- The result of `vote_resp_msg_type` is always in `{response}` and never in `{local}`.

---

## Edge Cases

- `MsgUnreachable` (value 10) appears in both classification sets — this is the only
  type with this property, confirmed by formal proof.
- `vote_resp_msg_type` is a partial function in Rust (panic on non-vote). The Lean
  model wraps the result in `Option` to make it total.

---

## Examples

| Input | `isLocalMsg` | `isResponseMsg` | `voteRespMsgType` |
|---|---|---|---|
| `MsgHup` | `true` | `false` | `none` |
| `MsgAppend` | `false` | `false` | `none` |
| `MsgAppendResponse` | `false` | `true` | `none` |
| `MsgUnreachable` | `true` | `true` | `none` |
| `MsgRequestVote` | `false` | `false` | `some MsgRequestVoteResponse` |
| `MsgRequestPreVote` | `false` | `false` | `some MsgRequestPreVoteResponse` |

---

## Open Questions

None — all 13 properties are fully determined by the source code and proved by `decide`.

---

*🔬 Lean Squad — automated formal verification.*
