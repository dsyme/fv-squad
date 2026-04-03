import FVSquad.JointCommittedIndex
import FVSquad.SafetyComposition

/-!
# Joint Safety Composition: JointCommittedIndex × HasQuorum × SafetyComposition

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Cross-module theorems extending the Raft log-safety result (**SC4**) from
single-majority configurations to **joint-quorum** configurations.

A joint configuration (Rust: `JointConfig { incoming, outgoing }`) commits an
index only when **both** constituent majority quorums commit it, so the joint
committed index is `min(committedIndex incoming, committedIndex outgoing)`.

## Core result

The principal theorem (`JSC7_joint_raft_log_safety`) is a **joint Raft log-safety
certificate**:

> For any two acked-index functions over the same joint configuration (same
> `incoming` and `outgoing` voter lists, both non-empty), there exist witness
> voters — one in `incoming`, one in `outgoing` — that individually acknowledged
> **both** joint committed indices.

Because any two majorities within the same half must intersect (proved by
`quorum_intersection`), no two divergent log prefixes can be simultaneously
committed under either half.  The joint requirement makes this even stronger:
both halves must independently certify each commitment, and both must share
cross-function witnesses.

## Theorem table

| ID   | Name                                    | Description                                                           |
|------|-----------------------------------------|-----------------------------------------------------------------------|
| JSC1 | `JSC1_jointCI_le_iff`                   | k ≤ jointCI ↔ k ≤ ci_in ∧ k ≤ ci_out                                |
| JSC2 | `JSC2_jointCI_iff_both_quorums`         | k ≤ jointCI ↔ k-quorum in both halves (non-empty)                    |
| JSC3 | `JSC3_jointCI_incoming_witness`         | ∃ voter in incoming that acknowledged jointCI                         |
| JSC4 | `JSC4_jointCI_outgoing_witness`         | ∃ voter in outgoing that acknowledged jointCI                         |
| JSC5 | `JSC5_joint_raft_log_safety_incoming`   | Two jointCIs share a witness voter in incoming                        |
| JSC6 | `JSC6_joint_raft_log_safety_outgoing`   | Two jointCIs share a witness voter in outgoing                        |
| JSC7 | `JSC7_joint_raft_log_safety`            | **Main**: witnesses exist in BOTH incoming and outgoing               |
| JSC8 | `JSC8_jointCI_maximality`               | k > jointCI → k-quorum fails in at least one half                    |
| JSC9 | `JSC9_jointCI_singleton`                | Singleton jointCI = min(acked vi, acked vo)                           |
| JSC10| `JSC10_joint_no_rollback`               | Committed index never decreases when acked indices increase pointwise |

## Modelling notes

- All models are purely functional; I/O, message passing, and concurrency are omitted.
- Voter IDs are `Nat` (Rust: `u64`); acked indices are `Nat` (Rust: `u64`).
- `AckedFn := Nat → Nat` models the `AckedIndexer` trait.
- Voter lists are `List Nat`; duplicates assumed absent where it matters.
- The known **empty-outgoing divergence** from `JointCommittedIndex.lean` applies:
  `committedIndex [] _ = 0` in this model, while Rust returns `u64::MAX`.
  Theorems JSC3–JSC7 require non-empty voter lists to avoid this degenerate case.
- **SC4** (from `SafetyComposition`) is used as a black box: it produces a
  concrete witness in each half independently; we then chain `jci ≤ ci_half`
  (from `jointCommittedIndex_le_in/out`) to transfer the witness property.
-/

open FVSquad.CommittedIndex
open FVSquad.JointCommittedIndex
open FVSquad.SafetyComposition

namespace FVSquad.JointSafetyComposition

/-! ## JSC1: Arithmetic characterisation -/

/-- **JSC1** — k ≤ jointCI iff k ≤ both constituent committed indices.

    Direct corollary of `jointCommittedIndex = min(ci_in, ci_out)` and `Nat.le_min`. -/
theorem JSC1_jointCI_le_iff
    (incoming outgoing : List Nat) (acked : AckedFn) (k : Nat) :
    k ≤ jointCommittedIndex incoming outgoing acked ↔
    k ≤ committedIndex incoming acked ∧ k ≤ committedIndex outgoing acked := by
  unfold jointCommittedIndex
  exact Nat.le_min

/-! ## JSC2: Quorum biconditional -/

/-- **JSC2** — For non-empty `incoming` and non-empty `outgoing`, the joint
    committed index is the largest k satisfying threshold quorums in **both** halves.

    Combines JSC1 with SC6 (the single-config biconditional) applied twice. -/
theorem JSC2_jointCI_iff_both_quorums
    (hi : Nat) (ti : List Nat) (ho : Nat) (to : List Nat)
    (acked : AckedFn) (k : Nat) :
    k ≤ jointCommittedIndex (hi :: ti) (ho :: to) acked ↔
    (hasQuorum (hi :: ti) (fun v => decide (acked v ≥ k)) = true ∧
     hasQuorum (ho :: to) (fun v => decide (acked v ≥ k)) = true) := by
  rw [JSC1_jointCI_le_iff]
  constructor
  · intro ⟨hin, hout⟩
    exact ⟨(SC6_committedIndex_quorum_iff hi ti acked k).mpr hin,
           (SC6_committedIndex_quorum_iff ho to acked k).mpr hout⟩
  · intro ⟨h1, h2⟩
    exact ⟨(SC6_committedIndex_quorum_iff hi ti acked k).mp h1,
           (SC6_committedIndex_quorum_iff ho to acked k).mp h2⟩

/-! ## JSC3–JSC4: Concrete witnesses for a single acked function -/

/-- **JSC3** — For non-empty `incoming`, there exists a voter that acknowledged
    the joint committed index.

    **Proof**: SC7 provides a voter witnessing `ci_in`.  Since `jci ≤ ci_in`
    (JCI1), that voter also witnesses `jci`. -/
theorem JSC3_jointCI_incoming_witness
    (hd : Nat) (tl outgoing : List Nat) (acked : AckedFn) :
    ∃ w ∈ (hd :: tl), acked w ≥ jointCommittedIndex (hd :: tl) outgoing acked := by
  obtain ⟨w, hmem, hw⟩ := SC7_committedIndex_witness hd tl acked
  exact ⟨w, hmem, Nat.le_trans (jointCommittedIndex_le_in (hd :: tl) outgoing acked) hw⟩

/-- **JSC4** — For non-empty `outgoing`, there exists a voter that acknowledged
    the joint committed index.  Symmetric to JSC3. -/
theorem JSC4_jointCI_outgoing_witness
    (hd : Nat) (tl : List Nat) (incoming : List Nat) (acked : AckedFn) :
    ∃ w ∈ (hd :: tl), acked w ≥ jointCommittedIndex incoming (hd :: tl) acked := by
  obtain ⟨w, hmem, hw⟩ := SC7_committedIndex_witness hd tl acked
  exact ⟨w, hmem, Nat.le_trans (jointCommittedIndex_le_out incoming (hd :: tl) acked) hw⟩

/-! ## JSC5–JSC6: Cross-function witnesses per half -/

/-- **JSC5** — For non-empty `incoming` and any two acked functions, there exists
    a voter in `incoming` that acknowledged **both** joint committed indices.

    **Proof**: SC4 produces a witness `w` satisfying `a1 w ≥ ci_in(a1)` and
    `a2 w ≥ ci_in(a2)`.  Since `jci(a1) ≤ ci_in(a1)` and `jci(a2) ≤ ci_in(a2)`,
    `w` also witnesses both joint committed indices. -/
theorem JSC5_joint_raft_log_safety_incoming
    (hd : Nat) (tl outgoing : List Nat) (a1 a2 : AckedFn) :
    ∃ w ∈ (hd :: tl),
      a1 w ≥ jointCommittedIndex (hd :: tl) outgoing a1 ∧
      a2 w ≥ jointCommittedIndex (hd :: tl) outgoing a2 := by
  obtain ⟨w, hmem, h1, h2⟩ := SC4_raft_log_safety hd tl a1 a2
  exact ⟨w, hmem,
    Nat.le_trans (jointCommittedIndex_le_in (hd :: tl) outgoing a1) h1,
    Nat.le_trans (jointCommittedIndex_le_in (hd :: tl) outgoing a2) h2⟩

/-- **JSC6** — For non-empty `outgoing` and any two acked functions, there exists
    a voter in `outgoing` that acknowledged **both** joint committed indices.

    Symmetric to JSC5, using `jointCommittedIndex_le_out` in place of
    `jointCommittedIndex_le_in`. -/
theorem JSC6_joint_raft_log_safety_outgoing
    (hd : Nat) (tl : List Nat) (incoming : List Nat) (a1 a2 : AckedFn) :
    ∃ w ∈ (hd :: tl),
      a1 w ≥ jointCommittedIndex incoming (hd :: tl) a1 ∧
      a2 w ≥ jointCommittedIndex incoming (hd :: tl) a2 := by
  obtain ⟨w, hmem, h1, h2⟩ := SC4_raft_log_safety hd tl a1 a2
  exact ⟨w, hmem,
    Nat.le_trans (jointCommittedIndex_le_out incoming (hd :: tl) a1) h1,
    Nat.le_trans (jointCommittedIndex_le_out incoming (hd :: tl) a2) h2⟩

/-! ## JSC7: Main theorem — joint Raft log safety -/

/-- **JSC7** — **Joint Raft log-safety certificate**.

    For non-empty `incoming` and non-empty `outgoing`, and any two acked-index
    functions `a1` and `a2` over the same voter configuration, there exist witness
    voters — one in each half — that individually acknowledged **both** joint
    committed indices simultaneously.

    Formally:
    - `∃ w_in ∈ incoming`, `a1 w_in ≥ jci1 ∧ a2 w_in ≥ jci2`  (JSC5)
    - `∃ w_out ∈ outgoing`, `a1 w_out ≥ jci1 ∧ a2 w_out ≥ jci2`  (JSC6)

    where `jciN = jointCommittedIndex incoming outgoing aN`.

    **Interpretation**: no two divergent log prefixes can both be jointly committed
    — any two committed prefixes are witnessed by a common voter in **each** half,
    preventing divergence under either majority quorum. -/
theorem JSC7_joint_raft_log_safety
    (hi : Nat) (ti : List Nat) (ho : Nat) (to : List Nat) (a1 a2 : AckedFn) :
    (∃ w_in ∈ (hi :: ti),
      a1 w_in ≥ jointCommittedIndex (hi :: ti) (ho :: to) a1 ∧
      a2 w_in ≥ jointCommittedIndex (hi :: ti) (ho :: to) a2) ∧
    (∃ w_out ∈ (ho :: to),
      a1 w_out ≥ jointCommittedIndex (hi :: ti) (ho :: to) a1 ∧
      a2 w_out ≥ jointCommittedIndex (hi :: ti) (ho :: to) a2) :=
  ⟨JSC5_joint_raft_log_safety_incoming hi ti (ho :: to) a1 a2,
   JSC6_joint_raft_log_safety_outgoing ho to (hi :: ti) a1 a2⟩

/-! ## JSC8: Maximality — no index above jointCI forms both quorums -/

/-- **JSC8** — For non-empty `incoming` and non-empty `outgoing`, any k strictly
    greater than the joint committed index fails to form a threshold quorum in at
    least one half.

    Equivalently: it is impossible for k > jointCI to form k-quorums in **both**
    halves simultaneously.

    **Proof**: if both quorums held, JSC2 would give `k ≤ jointCI`, a contradiction. -/
theorem JSC8_jointCI_maximality
    (hi : Nat) (ti : List Nat) (ho : Nat) (to : List Nat)
    (acked : AckedFn) (k : Nat)
    (hk : jointCommittedIndex (hi :: ti) (ho :: to) acked < k) :
    ¬ (hasQuorum (hi :: ti) (fun v => decide (acked v ≥ k)) = true ∧
       hasQuorum (ho :: to) (fun v => decide (acked v ≥ k)) = true) := by
  intro hboth
  have hle := (JSC2_jointCI_iff_both_quorums hi ti ho to acked k).mpr hboth
  omega

/-! ## JSC9: Singleton case -/

/-- **JSC9** — When `incoming = [vi]` and `outgoing = [vo]`, the joint committed
    index is `min (acked vi) (acked vo)`.

    **Proof**: by `committedIndex_singleton` applied to each half. -/
theorem JSC9_jointCI_singleton (vi vo : Nat) (acked : AckedFn) :
    jointCommittedIndex [vi] [vo] acked = min (acked vi) (acked vo) := by
  unfold jointCommittedIndex
  rw [committedIndex_singleton, committedIndex_singleton]

/-! ## JSC10: No rollback — committed index is monotone in acked values -/

/-- **JSC10** — The joint committed index is non-decreasing when all acked values
    increase pointwise.

    **Proof**: by `jointCommittedIndex_mono` (JCI7) from `JointCommittedIndex.lean`. -/
theorem JSC10_joint_no_rollback
    (incoming outgoing : List Nat) (a1 a2 : AckedFn)
    (hle : ∀ v, a1 v ≤ a2 v) :
    jointCommittedIndex incoming outgoing a1 ≤
    jointCommittedIndex incoming outgoing a2 :=
  jointCommittedIndex_mono incoming outgoing a1 a2 hle

/-! ## Evaluations -/

section Eval

-- JSC9: single-voter halves, acked = (vi↦5, vo↦3) → jointCI = min(5,3) = 3
#eval jointCommittedIndex [1] [2] (fun v => if v == 1 then 5 else 3)
-- expected: 3

-- JSC2 illustration: incoming [1,2,3] ack (1↦5, 2↦4, 3↦3), outgoing [4,5] ack (4↦3, 5↦5)
--   ci_in  = 4 (majority(3)=2; sorted desc [5,4,3]; index 1 = 4)
--   ci_out = 3 (majority(2)=2; sorted desc [5,3]; index 1 = 3)
--   jointCI = min(4,3) = 3
#eval jointCommittedIndex [1,2,3] [4,5]
    (fun v => if v == 1 then 5 else if v == 2 then 4 else if v == 4 then 3 else 5)
-- expected: 3

-- JSC8 illustration: k=4 > jointCI=3; check that quorum in outgoing fails at k=4
-- hasQuorum [4,5] (v ≥ 4) = overlapCount [4,5] (v ≥ 4): v=4 acks 3 < 4 → no; v=5 acks 5 ≥ 4 → yes
-- count = 1 < majority(2)=2 → false ✓
#eval hasQuorum [4, 5]
    (fun v => decide ((if v == 4 then (3 : Nat) else 5) ≥ 4))
-- expected: false

end Eval

end FVSquad.JointSafetyComposition
