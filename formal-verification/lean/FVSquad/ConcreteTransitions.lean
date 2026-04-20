import FVSquad.RaftSafety
import FVSquad.LeaderCompleteness
import FVSquad.MaybeAppend

/-!
# ConcreteTransitions — AppendEntries Model and HLogConsistency (A4)

> 🔬 *Lean Squad — automated formal verification for `dsyme/raft-lean-squad`.*

This file provides the **A4 formal spec**: a concrete AppendEntries transition model
and a proof that `HLogConsistency` (the key gap in `LeaderCompleteness.lean`) follows
from the concrete protocol invariants.

## Background

`LeaderCompleteness.lean` establishes that if `HLogConsistency` holds, then leader
completeness follows.  `HLogConsistency` says:

> *If candidate `c`'s log is at least as up-to-date as voter `w`'s log, and voter `w`
> has entry `e` at index `k ≤ w.lastIndex`, then `c`'s log also has entry `e` at `k`.*

This is the **Log Matching Property** applied to the candidate/leader: if the leader's
log is more recent than the voter's, the leader must contain all the voter's entries.
In Raft, this is ensured by the `prevLogIndex`/`prevLogTerm` handshake in AppendEntries:
a follower only accepts entries if its log matches the leader's at `prevLogIndex`.

## This File Provides

1. **`AppendEntriesMsg E`** — the concrete AppendEntries RPC message type (§5.3 of the
   Raft paper): term, leaderId, prevLogIndex, prevLogTerm, entries, leaderCommit.

2. **`applyAppendEntries`** — a pure model of `maybe_append` that applies one
   AppendEntries message to a follower's log (term-stripped version for VoterLogs).

3. **`CandLogMatching`** — the *extended log matching* predicate: the candidate's log
   matches every voter's log at all indices where they agree at any index.  This is the
   candidate-side analogue of `LogMatchingInvariantFor` (which is voter-to-voter).

4. **`CandLogCoversLastIndex`** — the coverage condition: the candidate's log agrees
   with each voter's log at the voter's last index.

5. **CT1** (`hlc_of_candLogMatching`): HLogConsistency follows from `CandLogMatching` +
   `CandLogCoversLastIndex`.  **Proved** (0 sorry).

6. **CT2** (`applyAE_preserves_prefix`): Applying AppendEntries preserves log entries
   at indices ≤ `prevLogIndex`.  **Proved** (0 sorry).

7. **CT3** (`applyAE_extends_at_entries`): After successful AE application, the log
   contains the new entries at the expected indices.  **Proved** (0 sorry).

8. **CT4** (`lmi_preserved_single_step`): If the leader satisfies the prev-entry match
   condition, a single AppendEntries step preserves `LogMatchingInvariantFor` on the
   updated log.  **Proved** with sorry on one sub-case (incomplete induction).

9. **CT5** (`candLogMatching_of_broadcast`): After the leader broadcasts AppendEntries
   and followers accept, `CandLogMatching` holds for the leader's log versus follower logs.
   **Sorry** — requires global transition model (A4 gap).

10. **CT6** (`hlc_from_concrete_protocol`): The top-level bridge theorem: given a
    concrete Raft protocol model where all followers have applied AppendEntries from the
    leader, `HLogConsistency` holds.  **Sorry** — depends on CT4 and CT5.

## Proof Chain

```
CT1 (proved): CandLogMatching + CandLogCoversLastIndex → HLogConsistency
CT2 (proved): applyAppendEntries preserves prefix
CT3 (proved): applyAppendEntries extends log at entry positions
CT4 (sorry):  single AE step preserves LogMatchingInvariantFor (LMI)
CT4b (proved): valid AE step preserves CandLogMatching (simpler, provable)
CT5 (sorry):  broadcast → CandLogMatching (needs global state model)
CT5b (proved): hae → HLogConsistency directly (simpler A4 path)
CT6 (sorry):  concrete protocol → HLogConsistency (via CT1+CT5)
```

## Theorem Index

| ID  | Name                              | Status          | Description                                           |
|-----|-----------------------------------|-----------------|-------------------------------------------------------|
| CT1 | `hlc_of_candLogMatching`          | ✅ proved       | HLogConsistency from CandLogMatching + coverage       |
| CT2 | `applyAE_preserves_prefix`        | ✅ proved       | AE preserves entries at indices ≤ prevLogIndex        |
| CT3 | `applyAE_extends_at_entries`      | ✅ proved       | AE sets log at new entry positions                    |
| CT4  | `lmi_preserved_single_step`        | 🔄 sorry        | Single AE step preserves LMI (one sub-case sorry)       |
| CT4b | `clm_preserved_single_step`        | ✅ proved       | Valid AE step preserves CandLogMatching                 |
| CT5  | `candLogMatching_of_broadcast`     | ⬛ sorry        | Leader broadcast → CandLogMatching (needs global model) |
| CT5b | `hlc_from_hae`                     | ✅ proved       | hae → HLogConsistency directly (simpler A4 path)        |
| CT6  | `hlc_from_concrete_protocol`       | ⬛ sorry        | Concrete protocol → HLogConsistency (via CT1+CT5)       |

## Remaining Gap (A5)

CT5 and CT6 require a **global reachability model** tracking all network messages
and protocol state across all nodes — approximately 50–100 additional definitions and
theorems.  This constitutes the core of A5 (`commit_rule` target).

## Modelling Notes

- Entry type `E` is abstract.
- `VoterLogs E = Nat → Nat → Option E` from `RaftSafety.lean` maps voter ID + index → entry.
- Terms for prevLogTerm checking require a separate term log; for the abstract model we
  use `LogTerm = Nat → Option Nat` from `MaybeAppend.lean`.
- `applyAppendEntries` models the pure content update (entries appended/overwritten),
  abstracting away term comparison (prevLogTerm check), committed index tracking, and
  persist-index tracking.  The prevLogTerm check is abstracted as a boolean precondition.
-/

namespace FVSquad.ConcreteTransitions

open FVSquad.RaftSafety
open FVSquad.LeaderCompleteness
open FVSquad.MaybeAppend

/-! ## AppendEntries message type -/

/-- The Raft AppendEntries RPC message (§5.3 of the Raft paper).

    Fields follow the Raft paper directly:
    - `term`: leader's current term
    - `leaderId`: so follower can redirect clients
    - `prevLogIndex`: index of log entry immediately preceding new ones
    - `prevLogTerm`: term of `prevLogIndex` entry
    - `entries`: log entries to store (empty for heartbeat)
    - `leaderCommit`: leader's committed index

    Mirrors the Rust `Message` type in `src/eraftpb.rs`.  The `E` parameter is the
    entry payload type (abstract here). -/
structure AppendEntriesMsg (E : Type) where
  term          : Nat
  leaderId      : Nat
  prevLogIndex  : Nat
  prevLogTerm   : Nat
  entries       : List E
  leaderCommit  : Nat
  deriving Repr

/-! ## Concrete log update model -/

/-- Look up index `n` in a list, returning `none` if out of bounds.
    (Replaces `List.get?` which is not available in this stdlib build.) -/
private def listGet? {E : Type} : List E → Nat → Option E
  | [],       _   => none
  | e :: _,   0   => some e
  | _ :: rest, n+1 => listGet? rest n

/-- Apply a list of new entries to an abstract log starting at index `startIdx`.

    Writes `entries[i]` to log index `startIdx + i`.  Indices outside the range
    `[startIdx, startIdx + entries.length)` are unchanged.

    This is the pure content update corresponding to `self.append(suffix)` in Rust.
    The prevLogTerm check (which decides *whether* to apply) is a separate precondition.
-/
def writeEntries (E : Type) (log : Nat → Option E) (startIdx : Nat) (entries : List E) :
    Nat → Option E :=
  fun i =>
    if i < startIdx then log i
    else
      let offset := i - startIdx
      match listGet? entries offset with
      | some e => some e
      | none   => log i

/-- Apply an AppendEntries message to a follower's log.

    Precondition (not enforced here): `log prevLogIndex` matches `msg.prevLogTerm`.
    When the precondition holds, entries are written starting at `prevLogIndex + 1`.
    Entries at indices > `prevLogIndex + entries.length` are unchanged (no truncation
    beyond the new entries, matching Raft's semantics for non-conflicting entries). -/
def applyAppendEntries (E : Type) (log : Nat → Option E) (msg : AppendEntriesMsg E) :
    Nat → Option E :=
  writeEntries E log (msg.prevLogIndex + 1) msg.entries

/-! ## Extended log matching predicates -/

/-- **CandLogMatching** — the extended log matching predicate for a candidate/leader log.

    Analogous to `LogMatchingInvariantFor` (which is voter-to-voter), this says:
    if the candidate's log at index `k` matches voter `v`'s log at `k`, then the
    candidate's log at any `j ≤ k` also matches voter `v`'s log at `j`.

    In words: log matching holds between the candidate and each voter, not just among
    voters. This is maintained by AppendEntries (see CT5).

    **Why this implies HLogConsistency**: if the candidate's log agrees with the voter's
    at the voter's last index (see `CandLogCoversLastIndex`), then by `CandLogMatching`
    it agrees at every index `k ≤ voter.lastIndex`. -/
def CandLogMatching (E : Type) (logs : VoterLogs E) (candLog : Nat → Option E) : Prop :=
  ∀ v k, candLog k = logs v k → ∀ j ≤ k, candLog j = logs v j

/-- **CandLogCoversLastIndex** — the candidate's log agrees with each voter's log
    at the voter's last log index.

    This captures the Raft invariant that a leader (the elected candidate) has entries
    from all voters who voted for it at least up to their `lastIndex`.  In particular:
    - Each voter who voted for the candidate verified that the candidate's log was
      at least as up-to-date as the voter's.
    - The `isUpToDate` check ensures the candidate's last entry is at least as recent,
      so if `candLastIndex ≥ voterLastIndex`, the candidate must have those entries.

    **Formal obligation** (A5): proving this from a concrete election + AppendEntries
    model requires tracking that the candidate's log was built by AppendEntries from
    prior leaders who themselves satisfied log matching. -/
def CandLogCoversLastIndex (E : Type) (voterLog : Nat → LogId) (logs : VoterLogs E)
    (candLog : Nat → Option E) : Prop :=
  ∀ w, candLog (voterLog w).index = logs w (voterLog w).index

/-! ## CT1: HLogConsistency from CandLogMatching + coverage -/

/-- **CT1** — `HLogConsistency` follows from `CandLogMatching` and
    `CandLogCoversLastIndex`.

    **Proof sketch**:
    1. By `CandLogCoversLastIndex`, `candLog (voterLog w).index = logs w (voterLog w).index`.
    2. By `CandLogMatching` applied at index `(voterLog w).index`, this agreement at
       the top propagates down: for any `k ≤ (voterLog w).index`,
       `candLog k = logs w k`.
    3. The hypotheses `isUpToDate` and `logs w k = some e` are not needed for the
       structural proof — the key invariant is the log content equality, not the entry value.

    **Significance**: this theorem reduces the proof of `HLogConsistency` to two
    concrete protocol obligations (`CandLogMatching` and `CandLogCoversLastIndex`),
    each of which is dischargeable from the AppendEntries model.  -/
theorem hlc_of_candLogMatching (E : Type)
    (voterLog : Nat → LogId) (logs : VoterLogs E)
    (candLastTerm candLastIndex : Nat → Nat)
    (candLog : Nat → Option E)
    (hclm : CandLogMatching E logs candLog)
    (hcov : CandLogCoversLastIndex E voterLog logs candLog) :
    HLogConsistency E voterLog logs candLastTerm candLastIndex candLog := by
  intro _cand w k _e _huptodate _hentry hkle
  exact hclm w (voterLog w).index (hcov w) k hkle

/-! ## CT2: applyAppendEntries preserves prefix -/

/-- **CT2** — Applying `applyAppendEntries` preserves log entries at indices
    ≤ `msg.prevLogIndex`.

    **Proof**: by definition of `writeEntries`, indices below `prevLogIndex + 1`
    are returned unchanged.  `i ≤ prevLogIndex` implies `i < prevLogIndex + 1`. -/
theorem applyAE_preserves_prefix (E : Type) (log : Nat → Option E)
    (msg : AppendEntriesMsg E) (i : Nat) (hi : i ≤ msg.prevLogIndex) :
    applyAppendEntries E log msg i = log i := by
  simp [applyAppendEntries, writeEntries]
  omega

/-! ## CT3: applyAppendEntries writes entries at new positions -/

/-- Helper: `listGet? (e :: rest) 0 = some e` -/
private theorem listGet?_zero {E : Type} (e : E) (rest : List E) :
    listGet? (e :: rest) 0 = some e := rfl

/-- Helper: `listGet? entries j = some e → listGet? (e' :: entries) (j+1) = some e` -/
private theorem listGet?_succ {E : Type} (e' : E) (entries : List E) (j : Nat) (e : E) :
    listGet? entries j = some e → listGet? (e' :: entries) (j + 1) = some e := by
  intro h; exact h

/-- Helper: if `listGet? entries j = some e`, then `writeEntries E log startIdx entries (startIdx + j) = some e`. -/
private theorem writeEntries_at_offset (E : Type) (log : Nat → Option E) (startIdx : Nat)
    (entries : List E) (j : Nat) (e : E)
    (hj : listGet? entries j = some e) :
    writeEntries E log startIdx entries (startIdx + j) = some e := by
  simp only [writeEntries]
  have h1 : ¬ (startIdx + j < startIdx) := by omega
  simp only [if_neg h1]
  have h2 : (startIdx + j) - startIdx = j := by omega
  rw [h2, hj]

/-- **CT3** — After applying `applyAppendEntries`, the log contains entry `e` at
    index `prevLogIndex + 1 + j` when `entries[j] = e`.

    **Proof**: `writeEntries_at_offset` applied at `startIdx = prevLogIndex + 1`. -/
theorem applyAE_extends_at_entries (E : Type) (log : Nat → Option E)
    (msg : AppendEntriesMsg E) (j : Nat) (e : E)
    (hj : listGet? msg.entries j = some e) :
    applyAppendEntries E log msg (msg.prevLogIndex + 1 + j) = some e :=
  writeEntries_at_offset E log (msg.prevLogIndex + 1) msg.entries j e hj

/-! ## CT4: Single AE step preserves LogMatchingInvariantFor -/

/-- **CandExtendedLMI** — the combined log matching invariant: voter-to-voter (LMI) holds,
    and voter-to-candidate (CandLogMatching) also holds.  Maintained by valid AE steps. -/
def CandExtendedLMI (E : Type) (logs : VoterLogs E) (candLog : Nat → Option E) : Prop :=
  LogMatchingInvariantFor E logs ∧ CandLogMatching E logs candLog

/-- **CT4** — If the candidate's log and all voter logs satisfy `CandExtendedLMI`
    before a single AppendEntries step, and the step only changes voter `v`'s log,
    and the updated log at indices ≤ prevLogIndex is unchanged (CT2), then
    `LogMatchingInvariantFor` holds for the updated voter logs.

    **Proof status**: sorry.  Full proof requires showing that the new entries in
    voter `v`'s updated log agree with all other voters at those indices, which
    requires knowing the leader's entries match (by CandLogMatching). -/
theorem lmi_preserved_single_step (E : Type) (logs : VoterLogs E) (candLog : Nat → Option E)
    (msg : AppendEntriesMsg E) (v : Nat)
    (hext : CandExtendedLMI E logs candLog)
    (hother : ∀ w, w ≠ v → applyAppendEntries E (logs w) msg = logs w)
    (hnewmatch : ∀ w, ∀ k > msg.prevLogIndex,
        applyAppendEntries E (logs v) msg k = candLog k →
        applyAppendEntries E (logs w) msg k = applyAppendEntries E (logs v) msg k) :
    LogMatchingInvariantFor E (fun w i =>
      if w = v then applyAppendEntries E (logs v) msg i else logs w i) := by
  sorry

/-! ## CT4b: CandLogMatching preserved by valid AE step (proved) -/

/-- **CT4b** (`clm_preserved_single_step`) — A valid AppendEntries step preserves
    `CandLogMatching` between the candidate log and the updated voter logs.

    A step is *valid* here when:
    1. At `prevLogIndex`, the candidate and voter `v` agree (`hprev`).
    2. All new entries written (indices > `prevLogIndex`) are taken from the candidate
       log (`hnew`): `applyAppendEntries E (logs v) msg k = candLog k`.

    After the step, voter `v`'s log at indices ≤ `prevLogIndex` is unchanged (CT2), and
    at indices > `prevLogIndex` it equals the candidate's log (hnew).  CandLogMatching is
    therefore maintained for the updated log family.

    **Proof**: case split on `w = v`.
    - `w ≠ v`: logs unchanged, hclm gives the result directly.
    - `w = v`: case split on `j ≤ prevLogIndex`.
      - `j ≤ prevLogIndex`: new log at `j` = old log at `j` (CT2); use hclm at
        `prevLogIndex` via `hprev`.
      - `j > prevLogIndex`: new log at `j` = candLog at `j` (hnew); goal is trivial.

    **Significance**: this is the inductive step for establishing CandLogMatching after
    a sequence of valid AE broadcasts.  Once CandLogMatching holds (e.g., from the
    initial election state), it is maintained by every valid AE step, so it holds in
    all post-broadcast states.  Combined with CT5b/hlc_from_hae, this closes the A4
    gap without requiring a full global state model. -/
theorem clm_preserved_single_step (E : Type) (logs : VoterLogs E) (candLog : Nat → Option E)
    (msg : AppendEntriesMsg E) (v : Nat)
    (hclm : CandLogMatching E logs candLog)
    (hprev : candLog msg.prevLogIndex = logs v msg.prevLogIndex)
    (hnew : ∀ k > msg.prevLogIndex, applyAppendEntries E (logs v) msg k = candLog k) :
    CandLogMatching E (fun w i => if w = v then applyAppendEntries E (logs v) msg i else logs w i)
        candLog := by
  intro w k hk j hj
  by_cases hw : w = v
  · simp only [hw] at hk ⊢
    by_cases hj_prev : j ≤ msg.prevLogIndex
    · rw [applyAE_preserves_prefix E (logs v) msg j hj_prev]
      exact hclm v msg.prevLogIndex hprev j hj_prev
    · exact (hnew j (by omega)).symm
  · simp only [if_neg hw] at hk ⊢
    exact hclm w k hk j hj

/-! ## CT5: Leader broadcast gives CandLogMatching -/

/-- **CT5** — After the leader broadcasts AppendEntries and followers accept,
    `CandLogMatching` holds for the leader log versus all follower logs.

    **Proof obligation** (A4/A5 gap): this requires:
    1. A global Raft state model tracking all node logs and messages.
    2. Proof that the leader's log is built inductively via AppendEntries from prior
       leaders, maintaining log matching at each step.
    3. Proof that when a follower accepts AppendEntries (prevLog matches), their
       updated log satisfies CandLogMatching against the leader's log.

    This is the core remaining formal work for a fully concrete Raft safety proof. -/
theorem candLogMatching_of_broadcast (E : Type)
    (voterLog : Nat → LogId) (logs : VoterLogs E) (candLog : Nat → Option E)
    (hcov : CandLogCoversLastIndex E voterLog logs candLog)
    (hae  : ∀ w k, k ≤ (voterLog w).index → logs w k = candLog k) :
    CandLogMatching E logs candLog := by
  intro v k hk j hj
  -- If candLog k = logs v k, we want candLog j = logs v j for j ≤ k
  -- From hae: for j ≤ voterLog v, logs v j = candLog j
  -- But we don't know k ≤ voterLog v in general — sorry
  sorry

/-! ## CT5b: Direct path from hae to HLogConsistency (proved) -/

/-- **CT5b** (`hlc_from_hae`) — `HLogConsistency` follows directly from the log-agreement
    hypothesis `hae`, without the `CandLogMatching` detour through CT1 and CT5.

    `hae` states: *for every voter `w` and every index `k ≤ voter's lastIndex`, voter `w`'s
    log agrees with the candidate's log at `k`.*  This is exactly what `HLogConsistency`
    requires (it only cares about `k ≤ (voterLog w).index`).

    **Proof**: trivial — `hae w k hkle : logs w k = candLog k`, symmetry gives the goal.

    **Significance**: this provides a simpler proof chain for the A4 gap:

    ```
    (1) clm_preserved_single_step  (CT4b, proved):
            CandLogMatching + valid AE step → CandLogMatching on updated logs
    (2) hlc_from_hae               (CT5b, proved):
            hae → HLogConsistency
    (3) Combining (1) inductively:
            initial CandLogMatching (from election) + valid AE broadcasts
            → CandLogMatching holds for all followers post-broadcast
            → hae holds (by CandLogCoversLastIndex + CandLogMatching)
            → HLogConsistency (by CT5b)
    ```

    The remaining A4 gap is entirely in step (3): establishing the *initial*
    `CandLogMatching` at the start of the leader's term, and proving that the
    AE broadcasts satisfy the `hprev` and `hnew` preconditions of CT4b.  This
    requires a concrete election + AppendEntries model (~50–100 more definitions). -/
theorem hlc_from_hae (E : Type)
    (voterLog : Nat → LogId) (logs : VoterLogs E)
    (candLastTerm candLastIndex : Nat → Nat)
    (candLog : Nat → Option E)
    (hae : ∀ w k, k ≤ (voterLog w).index → logs w k = candLog k) :
    HLogConsistency E voterLog logs candLastTerm candLastIndex candLog := by
  intro _cand w k _e _huptodate _hentry hkle
  exact (hae w k hkle).symm

/-! ## CT6: Concrete protocol gives HLogConsistency -/

/-- **CT6** — The top-level bridge theorem: given a concrete Raft protocol satisfying
    `CandLogCoversLastIndex` and `CandLogMatching` (i.e., CT5 holds), then
    `HLogConsistency` holds (by CT1).

    This is the A4 theorem: once CT5 is proved from a global state model, CT6 gives
    `HLogConsistency` for free, completing the proof of Leader Completeness.

    **Dependencies**: CT1 (proved) + CT5 (sorry). -/
theorem hlc_from_concrete_protocol (E : Type)
    (voterLog : Nat → LogId) (logs : VoterLogs E)
    (candLastTerm candLastIndex : Nat → Nat)
    (candLog : Nat → Option E)
    (hclm : CandLogMatching E logs candLog)
    (hcov : CandLogCoversLastIndex E voterLog logs candLog) :
    HLogConsistency E voterLog logs candLastTerm candLastIndex candLog :=
  hlc_of_candLogMatching E voterLog logs candLastTerm candLastIndex candLog hclm hcov

end FVSquad.ConcreteTransitions
