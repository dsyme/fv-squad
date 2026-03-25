/-!
# TickElection — Lean 4 Specification, Implementation, and Proofs

Models `RaftCore::tick_election` in `src/raft.rs` (lines ≈ 1103–1114):
the per-tick driver for the election timeout in Follower and Candidate state.

## Relevant Rust code

```rust
pub fn tick_election(&mut self) -> bool {
    self.election_elapsed += 1;
    if !self.pass_election_timeout() || !self.promotable {
        return false;
    }
    self.election_elapsed = 0;
    let m = new_message(INVALID_ID, MessageType::MsgHup, Some(self.id));
    let _ = self.step(m);
    true
}

pub fn pass_election_timeout(&self) -> bool {
    self.election_elapsed >= self.randomized_election_timeout
}
```

## Model scope and approximations

* We model only the timer-management and guard logic — not `step(MsgHup)`.
  The effect of `step(MsgHup)` (triggering an election, updating term, vote, etc.)
  is captured by a Boolean flag `election_fired` in `TickResult`.
* `election_elapsed` and `randomized_election_timeout` are modelled as `Nat`.
* `promotable : Bool` is taken as an input parameter (no config/log modelling here).
* The `randomized_election_timeout` is not re-randomised in this model; that happens
  inside `step → become_candidate → reset_randomized_election_timeout`, which is
  handled by `StateTransitions.lean`. Here we prove properties *before* any re-roll.
* I/O, message queuing, network, error handling — all omitted.

🔬 *Lean Squad — automated formal verification.*
-/

import Mathlib.Tactic

namespace FVSquad.TickElection

/-! ## Types -/

/-- Snapshot of the timer-relevant fields of a Raft node before `tick_election`. -/
structure ElectionState where
  /-- Ticks elapsed since last election reset. -/
  election_elapsed : Nat
  /-- Randomised election timeout in `[min_election_timeout, max_election_timeout)`. -/
  randomized_election_timeout : Nat
  /-- True iff this node is a voter (not a learner) in the current config. -/
  promotable : Bool

/-- Outcome of one call to `tick_election`. -/
structure TickResult where
  /-- Updated `election_elapsed` after the call. -/
  election_elapsed : Nat
  /-- Whether `tick_election` returned `true` (i.e. a `MsgHup` was enqueued). -/
  fired : Bool

/-! ## Implementation model -/

/-- Pure model of `pass_election_timeout`. -/
def passElectionTimeout (s : ElectionState) : Bool :=
  s.election_elapsed ≥ s.randomized_election_timeout

/-- Pure model of `tick_election`.
    Returns `(new_elapsed, fired)`.
    Does NOT model the internal `step(MsgHup)` call — only the timer logic. -/
def tickElection (s : ElectionState) : TickResult :=
  let new_elapsed := s.election_elapsed + 1
  if new_elapsed ≥ s.randomized_election_timeout ∧ s.promotable then
    { election_elapsed := 0, fired := true }
  else
    { election_elapsed := new_elapsed, fired := false }

/-! ## Helper lemmas -/

@[simp]
theorem tickElection_fired_iff (s : ElectionState) :
    (tickElection s).fired = true ↔
    s.election_elapsed + 1 ≥ s.randomized_election_timeout ∧ s.promotable = true := by
  simp [tickElection]
  split_ifs with h
  · simp [h]
  · push_neg at h
    simp
    intro h1 h2
    exact h ⟨h1, h2⟩

@[simp]
theorem tickElection_elapsed_when_fired (s : ElectionState)
    (h : (tickElection s).fired = true) :
    (tickElection s).election_elapsed = 0 := by
  simp [tickElection] at *
  split_ifs with hc at h ⊢ <;> simp_all

@[simp]
theorem tickElection_elapsed_when_not_fired (s : ElectionState)
    (h : (tickElection s).fired = false) :
    (tickElection s).election_elapsed = s.election_elapsed + 1 := by
  simp [tickElection] at *
  split_ifs with hc at h ⊢ <;> simp_all

/-! ## Main propositions (P1–P6 from the informal spec) -/

/-- **P1** `tick_election_increments_elapsed`:
    The elapsed counter increases by 1 before the guard check.
    Equivalently: the result is either `old+1` (no fire) or `0` (fire). -/
theorem p1_elapsed_always_incremented (s : ElectionState) :
    let r := tickElection s
    r.election_elapsed = s.election_elapsed + 1 ∨ r.election_elapsed = 0 := by
  simp [tickElection]
  split_ifs <;> simp

/-- **P2** `tick_election_fires_iff`:
    Fires if and only if timeout passed AND node is promotable. -/
theorem p2_fires_iff (s : ElectionState) :
    (tickElection s).fired = true ↔
    s.election_elapsed + 1 ≥ s.randomized_election_timeout ∧ s.promotable = true := by
  simp [tickElection]
  split_ifs with h
  · simp [h]
  · push_neg at h
    constructor
    · intro hf; simp at hf
    · intro ⟨h1, h2⟩; exact absurd ⟨h1, h2⟩ h

/-- **P3** `tick_election_resets_on_fire`:
    When fired, `election_elapsed` is reset to 0. -/
theorem p3_resets_when_fired (s : ElectionState) :
    (tickElection s).fired = true →
    (tickElection s).election_elapsed = 0 := by
  simp [tickElection]
  split_ifs with h <;> simp_all

/-- **P4** `tick_election_no_reset_on_false`:
    When not fired, `election_elapsed` is exactly `old + 1`. -/
theorem p4_no_reset_when_false (s : ElectionState) :
    (tickElection s).fired = false →
    (tickElection s).election_elapsed = s.election_elapsed + 1 := by
  simp [tickElection]
  split_ifs with h <;> simp_all

/-- **P5** `tick_election_nonpromotable_false`:
    A non-promotable node never fires an election. -/
theorem p5_nonpromotable_never_fires (s : ElectionState) (hp : s.promotable = false) :
    (tickElection s).fired = false := by
  simp [tickElection, hp]
  split_ifs with h
  · simp [hp] at h
  · rfl

/-- **P6** `tick_election_below_timeout_false`:
    If the incremented counter is still below the timeout, no election fires. -/
theorem p6_below_timeout_no_fire (s : ElectionState)
    (h : s.election_elapsed + 1 < s.randomized_election_timeout) :
    (tickElection s).fired = false := by
  simp [tickElection]
  split_ifs with hc
  · omega
  · rfl

/-! ## Derived properties -/

/-- A promotable node with elapsed at least `timeout - 1` fires on the next tick. -/
theorem promotable_at_threshold_fires (s : ElectionState)
    (hp : s.promotable = true)
    (he : s.election_elapsed + 1 ≥ s.randomized_election_timeout) :
    (tickElection s).fired = true := by
  simp [tickElection, hp, he]

/-- After firing, `election_elapsed = 0 < randomized_election_timeout`
    (assuming timeout > 0), so the *next* call will not fire
    (unless timeout = 0, which is nonsensical). -/
theorem after_fire_not_immediately_refires
    (s : ElectionState)
    (hfire : (tickElection s).fired = true)
    (htimeout : s.randomized_election_timeout > 1) :
    let s' : ElectionState :=
      { s with election_elapsed := (tickElection s).election_elapsed }
    (tickElection s').fired = false := by
  have hreset := p3_resets_when_fired s hfire
  simp [tickElection, hreset]
  split_ifs with h
  · obtain ⟨hge, _⟩ := h
    omega
  · rfl

/-- The result of a non-firing tick keeps the counter strictly below the counter
    that would cause the *next* tick to fire, only if `promotion_check` short-circuits. -/
theorem no_fire_elapsed_increases (s : ElectionState)
    (hf : (tickElection s).fired = false) :
    (tickElection s).election_elapsed > s.election_elapsed := by
  have := p4_no_reset_when_false s hf
  omega

/-- Two consecutive non-firing ticks each increment the counter. -/
theorem two_consecutive_no_fires (s : ElectionState)
    (hf1 : (tickElection s).fired = false) :
    let s' : ElectionState :=
      { s with election_elapsed := (tickElection s).election_elapsed }
    (tickElection s').fired = false →
    (tickElection s').election_elapsed = s.election_elapsed + 2 := by
  intro s'
  have h1 := p4_no_reset_when_false s hf1
  intro hf2
  have h2 := p4_no_reset_when_false s' hf2
  simp [s'] at h2
  omega

end FVSquad.TickElection
