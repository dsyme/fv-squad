/-!
# MessageType Classification — Lean 4 Specification

Formal specification and proofs of the three message-type classification
functions from `src/raw_node.rs` and `src/raft.rs`:

* `is_local_msg` — identifies messages generated internally (not sent on the wire)
* `is_response_msg` — identifies reply messages from peers
* `vote_resp_msg_type` — maps a vote-request type to its corresponding response type

## Model scope and approximations

* **`MsgType`**: The 19-variant enum is defined as a plain inductive type
  mirroring the `MessageType` protobuf enum in `proto/proto/eraftpb.proto`.
  The numeric values (0–18) are not modelled; only the names matter here.
* **`vote_resp_msg_type`**: The Rust function panics on non-vote inputs.
  The Lean model returns `Option MsgType` (`none` for non-vote inputs)
  to avoid partiality. All proved properties use the `some` branches.
* **Omitted**: message routing logic, `step`, `send` — only the pure
  classification functions are modelled.

All propositions in this file are proved by `decide` (the type is finite and
all predicates are decidable). No `sorry`.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Tactic

namespace FVSquad.MsgType

/-! ## Message type enum -/

/-- Lean mirror of the `MessageType` protobuf enum (`proto/proto/eraftpb.proto`).
    19 variants, values 0–18. -/
inductive MsgType where
  | MsgHup                    -- 0  election timeout trigger (local)
  | MsgBeat                   -- 1  heartbeat timeout trigger (local)
  | MsgPropose                -- 2  client proposal
  | MsgAppend                 -- 3  log replication from leader
  | MsgAppendResponse         -- 4  follower reply to MsgAppend
  | MsgRequestVote            -- 5  vote request (real election)
  | MsgRequestVoteResponse    -- 6  vote reply
  | MsgSnapshot               -- 7  leader sends full snapshot
  | MsgHeartbeat              -- 8  leader heartbeat
  | MsgHeartbeatResponse      -- 9  follower heartbeat reply
  | MsgUnreachable            -- 10 transport: peer unreachable (local + response)
  | MsgSnapStatus             -- 11 snapshot delivery status (local)
  | MsgCheckQuorum            -- 12 periodic quorum-check trigger (local)
  | MsgTransferLeader         -- 13 leadership transfer request
  | MsgTimeoutNow             -- 14 tell transferee to start election now
  | MsgReadIndex              -- 15 linearizable read request
  | MsgReadIndexResp          -- 16 read-index response
  | MsgRequestPreVote         -- 17 pre-vote request (pre-election)
  | MsgRequestPreVoteResponse -- 18 pre-vote reply
  deriving DecidableEq, Repr, BEq, Inhabited

/-! ## Classification predicates -/

/-- `is_local_msg`: messages produced internally; never sent over the network. -/
def isLocalMsg (t : MsgType) : Bool :=
  match t with
  | .MsgHup | .MsgBeat | .MsgUnreachable | .MsgSnapStatus | .MsgCheckQuorum => true
  | _ => false

/-- `is_response_msg`: messages that are replies from peers. -/
def isResponseMsg (t : MsgType) : Bool :=
  match t with
  | .MsgAppendResponse | .MsgRequestVoteResponse | .MsgHeartbeatResponse
  | .MsgUnreachable    | .MsgRequestPreVoteResponse => true
  | _ => false

/-- `vote_resp_msg_type`: maps a vote-request to its vote-response.
    Returns `none` for non-vote inputs (in Rust: panic). -/
def voteRespMsgType (t : MsgType) : Option MsgType :=
  match t with
  | .MsgRequestVote    => some .MsgRequestVoteResponse
  | .MsgRequestPreVote => some .MsgRequestPreVoteResponse
  | _                  => none

/-! ## Propositions -/

/-- PROP-1  `isLocalMsg` is exactly `{MsgHup, MsgBeat, MsgUnreachable, MsgSnapStatus, MsgCheckQuorum}`. -/
theorem isLocalMsg_iff (t : MsgType) :
    isLocalMsg t = true ↔
    t = .MsgHup ∨ t = .MsgBeat ∨ t = .MsgUnreachable ∨
    t = .MsgSnapStatus ∨ t = .MsgCheckQuorum := by
  decide

/-- PROP-2  `isResponseMsg` is exactly `{MsgAppendResponse, MsgRequestVoteResponse,
    MsgHeartbeatResponse, MsgUnreachable, MsgRequestPreVoteResponse}`. -/
theorem isResponseMsg_iff (t : MsgType) :
    isResponseMsg t = true ↔
    t = .MsgAppendResponse ∨ t = .MsgRequestVoteResponse ∨
    t = .MsgHeartbeatResponse ∨ t = .MsgUnreachable ∨
    t = .MsgRequestPreVoteResponse := by
  decide

/-- PROP-3  The overlap of local and response is exactly `{MsgUnreachable}`.

    `MsgUnreachable` is intentionally in both: it is locally triggered by the
    transport layer AND acts as a pseudo-response that advances the leader's
    replication pipeline. -/
theorem local_response_overlap (t : MsgType) :
    (isLocalMsg t = true ∧ isResponseMsg t = true) ↔ t = .MsgUnreachable := by
  decide

/-- PROP-4  The two sets cover different parts of the protocol; all types outside
    both sets are "request" messages (sent from leader/candidate outward). -/
theorem neither_local_nor_response (t : MsgType) :
    isLocalMsg t = false → isResponseMsg t = false →
    t = .MsgPropose      ∨ t = .MsgAppend         ∨ t = .MsgRequestVote ∨
    t = .MsgSnapshot     ∨ t = .MsgHeartbeat       ∨ t = .MsgTransferLeader ∨
    t = .MsgTimeoutNow   ∨ t = .MsgReadIndex       ∨ t = .MsgReadIndexResp ∨
    t = .MsgRequestPreVote := by
  decide

/-- PROP-5  `voteRespMsgType MsgRequestVote = some MsgRequestVoteResponse`. -/
@[simp]
theorem voteRespMsgType_vote :
    voteRespMsgType .MsgRequestVote = some .MsgRequestVoteResponse := by
  decide

/-- PROP-6  `voteRespMsgType MsgRequestPreVote = some MsgRequestPreVoteResponse`. -/
@[simp]
theorem voteRespMsgType_prevote :
    voteRespMsgType .MsgRequestPreVote = some .MsgRequestPreVoteResponse := by
  decide

/-- PROP-7  `voteRespMsgType` returns `none` for all non-vote types. -/
theorem voteRespMsgType_none (t : MsgType)
    (ht : t ≠ .MsgRequestVote ∧ t ≠ .MsgRequestPreVote) :
    voteRespMsgType t = none := by
  have h1 := ht.1; have h2 := ht.2
  revert h1 h2
  cases t <;> simp [voteRespMsgType]

/-- PROP-8  The result of `voteRespMsgType` (when `some`) is always a response message. -/
theorem voteRespMsgType_is_response (t : MsgType) (r : MsgType)
    (h : voteRespMsgType t = some r) :
    isResponseMsg r = true := by
  revert h
  cases t <;> simp [voteRespMsgType, isResponseMsg]

/-- PROP-9  The result of `voteRespMsgType` (when `some`) is NOT a local message. -/
theorem voteRespMsgType_not_local (t : MsgType) (r : MsgType)
    (h : voteRespMsgType t = some r) :
    isLocalMsg r = false := by
  revert h
  cases t <;> simp [voteRespMsgType, isLocalMsg]

/-- PROP-10  There are exactly 5 local messages. -/
theorem count_local_msgs :
    (List.filter isLocalMsg
      [.MsgHup, .MsgBeat, .MsgPropose, .MsgAppend, .MsgAppendResponse,
       .MsgRequestVote, .MsgRequestVoteResponse, .MsgSnapshot, .MsgHeartbeat,
       .MsgHeartbeatResponse, .MsgUnreachable, .MsgSnapStatus, .MsgCheckQuorum,
       .MsgTransferLeader, .MsgTimeoutNow, .MsgReadIndex, .MsgReadIndexResp,
       .MsgRequestPreVote, .MsgRequestPreVoteResponse]).length = 5 := by
  decide

/-- PROP-11  There are exactly 5 response messages. -/
theorem count_response_msgs :
    (List.filter isResponseMsg
      [.MsgHup, .MsgBeat, .MsgPropose, .MsgAppend, .MsgAppendResponse,
       .MsgRequestVote, .MsgRequestVoteResponse, .MsgSnapshot, .MsgHeartbeat,
       .MsgHeartbeatResponse, .MsgUnreachable, .MsgSnapStatus, .MsgCheckQuorum,
       .MsgTransferLeader, .MsgTimeoutNow, .MsgReadIndex, .MsgReadIndexResp,
       .MsgRequestPreVote, .MsgRequestPreVoteResponse]).length = 5 := by
  decide

/-- PROP-12  There are exactly 2 vote-request types (domain of `voteRespMsgType`). -/
theorem count_vote_request_types :
    (List.filter (fun t => (voteRespMsgType t).isSome)
      [.MsgHup, .MsgBeat, .MsgPropose, .MsgAppend, .MsgAppendResponse,
       .MsgRequestVote, .MsgRequestVoteResponse, .MsgSnapshot, .MsgHeartbeat,
       .MsgHeartbeatResponse, .MsgUnreachable, .MsgSnapStatus, .MsgCheckQuorum,
       .MsgTransferLeader, .MsgTimeoutNow, .MsgReadIndex, .MsgReadIndexResp,
       .MsgRequestPreVote, .MsgRequestPreVoteResponse]).length = 2 := by
  decide

/-- PROP-13  `voteRespMsgType` is injective on its domain (different vote types → different responses). -/
theorem voteRespMsgType_injective (s t : MsgType) (rs rt : MsgType)
    (hs : voteRespMsgType s = some rs) (ht : voteRespMsgType t = some rt)
    (heq : rs = rt) : s = t := by
  revert hs ht
  cases s <;> cases t <;> simp [voteRespMsgType] <;> try exact heq ▸ rfl

/-! ## Examples -/

#eval isLocalMsg .MsgHup          -- true
#eval isLocalMsg .MsgAppend        -- false
#eval isResponseMsg .MsgAppendResponse    -- true
#eval isResponseMsg .MsgUnreachable       -- true  (also local!)
#eval isLocalMsg .MsgUnreachable          -- true  (also response!)
#eval voteRespMsgType .MsgRequestVote     -- some MsgRequestVoteResponse
#eval voteRespMsgType .MsgRequestPreVote  -- some MsgRequestPreVoteResponse
#eval voteRespMsgType .MsgAppend          -- none

end FVSquad.MsgType
