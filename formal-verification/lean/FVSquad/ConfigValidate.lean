/-!
# ConfigValidate — Lean 4 Specification and Implementation Model

Formal specification of `Config::validate` from `raft-rs` (`src/config.rs`).

`Config::validate` checks eight structural invariants that a Raft configuration
must satisfy before a node can be started. It is a pure, total function that
returns `Ok(())` if all constraints pass, or `Err(...)` on the first violation
(short-circuit evaluation).

## Constraints

| # | Name | Condition |
|---|------|-----------|
| C1 | id_nonzero        | `id ≠ 0`                                              |
| C2 | hb_positive       | `heartbeat_tick ≥ 1`                                  |
| C3 | election_gt_hb    | `election_tick > heartbeat_tick`                      |
| C4 | min_tick_ge_et    | `minElectionTick ≥ election_tick`                     |
| C5 | min_lt_max        | `minElectionTick < maxElectionTick`                   |
| C6 | inflight_positive | `max_inflight_msgs ≥ 1`                               |
| C7 | lease_needs_quorum| `read_only_option = LeaseBased → check_quorum = true` |
| C8 | uncommitted_ge    | `max_uncommitted_size ≥ max_size_per_msg`             |

## Model scope and approximations

* **Types**: `usize` and `u64` fields are modelled as `Nat` (no overflow, no 64-bit bound).
  The `NO_LIMIT = u64::MAX` sentinel for `max_uncommitted_size` is simply a large `Nat`.
* **Return type**: the Rust function returns `Result<()>`. The Lean model uses `Bool`
  (`true` = `Ok(())`, `false` = `Err(...)`). Error messages are not modelled.
* **Short-circuit evaluation**: the Rust function returns on the first failure. The Lean
  model uses `&&` (lazy Boolean conjunction), which has the same observable semantics.
* **Omitted fields**: `applied`, `priority`, `skip_bcast_commit`, `batch_append`,
  `pre_vote`, `max_committed_size_per_ready`, `max_apply_unpersisted_log_limit`,
  `disable_proposal_forwarding` — none are checked by `validate`.

🔬 *Lean Squad — auto-generated formal specification and implementation model.*
-/

import Mathlib.Tactic

namespace FVSquad.ConfigValidate

/-! ## Types -/

/-- Read-only mode, mirroring `ReadOnlyOption` from `src/raft.rs`.
    `Safe`: linear reads (default). `ReadIndex`: read-index protocol.
    `LeaseBased`: lease-based reads (requires `check_quorum`). -/
inductive ReadOnlyOption where
  | Safe       : ReadOnlyOption
  | ReadIndex  : ReadOnlyOption
  | LeaseBased : ReadOnlyOption
  deriving DecidableEq, Repr

/-- Lean model of the `Config` fields checked by `validate`.
    All `usize`/`u64` fields are `Nat`.  The default values from `Config::default()` are:
    `heartbeat_tick = 2`, `election_tick = 20`, `max_inflight_msgs = 256`,
    `max_uncommitted_size = NO_LIMIT ≈ u64::MAX`, `max_size_per_msg = 0`,
    `min_election_tick = 0` (→ use `election_tick`),
    `max_election_tick = 0` (→ use `2 * election_tick`),
    `id = 0` (invalid — only failing constraint in the default config),
    `read_only_option = Safe`, `check_quorum = false`. -/
structure Config where
  id                   : Nat         -- node ID; 0 is the INVALID_ID sentinel
  heartbeat_tick       : Nat         -- ticks between leader heartbeats
  election_tick        : Nat         -- ticks before follower election timeout
  max_inflight_msgs    : Nat         -- max unacknowledged messages per peer
  max_uncommitted_size : Nat         -- max total byte size of uncommitted entries
  max_size_per_msg     : Nat         -- max byte size of a single message
  min_election_tick    : Nat         -- 0 ⇒ use election_tick as the effective minimum
  max_election_tick    : Nat         -- 0 ⇒ use 2 * election_tick as the effective maximum
  read_only_option     : ReadOnlyOption
  check_quorum         : Bool
  deriving Repr

/-! ## Helper functions -/

/-- Effective minimum election timeout.
    Mirrors `Config::min_election_tick()`: uses `election_tick` when the field is 0. -/
def Config.minElectionTick (c : Config) : Nat :=
  if c.min_election_tick == 0 then c.election_tick else c.min_election_tick

/-- Effective maximum election timeout.
    Mirrors `Config::max_election_tick()`: uses `2 * election_tick` when the field is 0. -/
def Config.maxElectionTick (c : Config) : Nat :=
  if c.max_election_tick == 0 then 2 * c.election_tick else c.max_election_tick

/-! ## Individual constraint predicates -/

/-- C1: node id must not be 0 (INVALID_ID sentinel). -/
def c1 (c : Config) : Bool := c.id != 0

/-- C2: heartbeat tick must be positive. -/
def c2 (c : Config) : Bool := c.heartbeat_tick != 0

/-- C3: election tick must be strictly greater than heartbeat tick. -/
def c3 (c : Config) : Bool := c.heartbeat_tick < c.election_tick

/-- C4: effective minimum election timeout ≥ election tick. -/
def c4 (c : Config) : Bool := c.election_tick ≤ c.minElectionTick

/-- C5: effective minimum election timeout < effective maximum election timeout. -/
def c5 (c : Config) : Bool := c.minElectionTick < c.maxElectionTick

/-- C6: max inflight messages must be positive. -/
def c6 (c : Config) : Bool := c.max_inflight_msgs != 0

/-- C7: LeaseBased read-only option requires check_quorum to be enabled. -/
def c7 (c : Config) : Bool :=
  !(c.read_only_option == ReadOnlyOption.LeaseBased) || c.check_quorum

/-- C8: max uncommitted size must be at least as large as max size per message.
    (Ensures the proposal queue can always hold at least one full message.) -/
def c8 (c : Config) : Bool := c.max_size_per_msg ≤ c.max_uncommitted_size

/-! ## Main function: `validateConfig` -/

/-- `validateConfig c = true` iff `c` satisfies all eight validation constraints.
    Mirrors `Config::validate` from `src/config.rs`.

    The constraints are evaluated left-to-right; `&&` short-circuits on the first failure,
    matching the Rust implementation which returns `Err` on the first violation. -/
def validateConfig (c : Config) : Bool :=
  c1 c && c2 c && c3 c && c4 c && c5 c && c6 c && c7 c && c8 c

/-! ## Sanity checks via `decide` -/

-- Valid config: id=1, heartbeat=2, election=20, defaults for tick range, inflight=256, NO_LIMIT
example : validateConfig ⟨1, 2, 20, 256, 0xFFFFFFFF, 0, 0, 0, .Safe, false⟩ = true := by decide

-- C1 fails: id = 0 (the default config without setting id)
example : validateConfig ⟨0, 2, 20, 256, 100, 0, 0, 0, .Safe, false⟩ = false := by decide

-- C3 fails: election_tick = heartbeat_tick (not strictly greater)
example : validateConfig ⟨1, 5, 5, 1, 100, 0, 0, 0, .Safe, false⟩ = false := by decide

-- C4 fails: min_election_tick < election_tick
example : validateConfig ⟨1, 1, 10, 1, 100, 0, 8, 20, .Safe, false⟩ = false := by decide

-- C7 fails: LeaseBased without check_quorum
example : validateConfig ⟨1, 1, 2, 1, 100, 0, 0, 0, .LeaseBased, false⟩ = false := by decide

-- C7 OK: LeaseBased WITH check_quorum
example : validateConfig ⟨1, 1, 2, 1, 100, 0, 0, 0, .LeaseBased, true⟩ = true := by decide

-- C7 OK: Safe does not require check_quorum
example : validateConfig ⟨1, 1, 2, 1, 100, 0, 0, 0, .Safe, false⟩ = true := by decide

-- C8 fails: max_size_per_msg > max_uncommitted_size
example : validateConfig ⟨1, 1, 2, 1, 50, 100, 0, 0, .Safe, false⟩ = false := by decide

-- C8 trivially OK when max_size_per_msg = 0
example : validateConfig ⟨1, 1, 2, 1, 0, 0, 0, 0, .Safe, false⟩ = true := by decide

/-! ## Helper lemmas for `minElectionTick` and `maxElectionTick` -/

private lemma minElectionTick_default (c : Config) (h : c.min_election_tick = 0) :
    c.minElectionTick = c.election_tick := by
  simp [Config.minElectionTick, h]

private lemma minElectionTick_custom (c : Config) (h : c.min_election_tick ≠ 0) :
    c.minElectionTick = c.min_election_tick := by
  simp only [Config.minElectionTick]
  split_ifs with heq
  · simp at heq; exact absurd heq h
  · rfl

private lemma maxElectionTick_default (c : Config) (h : c.max_election_tick = 0) :
    c.maxElectionTick = 2 * c.election_tick := by
  simp [Config.maxElectionTick, h]

private lemma maxElectionTick_custom (c : Config) (h : c.max_election_tick ≠ 0) :
    c.maxElectionTick = c.max_election_tick := by
  simp only [Config.maxElectionTick]
  split_ifs with heq
  · simp at heq; exact absurd heq h
  · rfl

/-! ## Core soundness theorems (C1–C8) -/

-- Technical helper: extract the 7th-from-outermost element of the and-chain
private lemma validateConfig_unpack (c : Config) (h : validateConfig c = true) :
    c1 c = true ∧ c2 c = true ∧ c3 c = true ∧ c4 c = true ∧
    c5 c = true ∧ c6 c = true ∧ c7 c = true ∧ c8 c = true := by
  simp only [validateConfig, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **C1 soundness**: if `validateConfig c = true`, then `c.id ≠ 0`. -/
theorem validate_id (c : Config) (h : validateConfig c = true) : c.id ≠ 0 := by
  have ⟨h1, _⟩ := validateConfig_unpack c h
  simp [c1, bne_iff_ne] at h1
  exact h1

/-- **C2 soundness**: if `validateConfig c = true`, then `c.heartbeat_tick ≥ 1`. -/
theorem validate_hb (c : Config) (h : validateConfig c = true) : c.heartbeat_tick ≥ 1 := by
  have ⟨_, h2, _⟩ := validateConfig_unpack c h
  simp [c2, bne_iff_ne] at h2
  omega

/-- **C3 soundness**: if `validateConfig c = true`, then `c.election_tick > c.heartbeat_tick`. -/
theorem validate_election_gt_hb (c : Config) (h : validateConfig c = true) :
    c.election_tick > c.heartbeat_tick := by
  have ⟨_, _, h3, _⟩ := validateConfig_unpack c h
  simp only [c3, decide_eq_true_eq] at h3
  exact h3

/-- **C4 soundness**: if `validateConfig c = true`, then `minElectionTick c ≥ election_tick`. -/
theorem validate_min_election (c : Config) (h : validateConfig c = true) :
    c.minElectionTick ≥ c.election_tick := by
  have ⟨_, _, _, h4, _⟩ := validateConfig_unpack c h
  simp only [c4, decide_eq_true_eq] at h4
  exact h4

/-- **C5 soundness**: if `validateConfig c = true`, then `minElectionTick c < maxElectionTick c`. -/
theorem validate_tick_range (c : Config) (h : validateConfig c = true) :
    c.minElectionTick < c.maxElectionTick := by
  have ⟨_, _, _, _, h5, _⟩ := validateConfig_unpack c h
  simp only [c5, decide_eq_true_eq] at h5
  exact h5

/-- **C6 soundness**: if `validateConfig c = true`, then `c.max_inflight_msgs ≥ 1`. -/
theorem validate_inflight (c : Config) (h : validateConfig c = true) :
    c.max_inflight_msgs ≥ 1 := by
  have ⟨_, _, _, _, _, h6, _⟩ := validateConfig_unpack c h
  simp [c6, bne_iff_ne] at h6
  omega

/-- **C7 soundness**: if `validateConfig c = true` and `read_only_option = LeaseBased`,
    then `check_quorum = true`. -/
theorem validate_lease (c : Config) (h : validateConfig c = true) :
    c.read_only_option = .LeaseBased → c.check_quorum = true := by
  have ⟨_, _, _, _, _, _, h7, _⟩ := validateConfig_unpack c h
  intro heq
  -- Substitute the concrete value; the constraint reduces to: c.check_quorum = true
  subst heq
  simp only [c7, Bool.beq_self_eq_true, Bool.not_true, Bool.false_or] at h7
  exact h7

/-- **C8 soundness**: if `validateConfig c = true`, then
    `c.max_uncommitted_size ≥ c.max_size_per_msg`. -/
theorem validate_uncommitted (c : Config) (h : validateConfig c = true) :
    c.max_uncommitted_size ≥ c.max_size_per_msg := by
  have ⟨_, _, _, _, _, _, _, h8⟩ := validateConfig_unpack c h
  simp only [c8, decide_eq_true_eq] at h8
  exact h8

/-! ## Exact characterisation: `validate_ok_iff` -/

/-- **Exact characterisation**: `validateConfig c = true` iff all eight constraints hold.

    This is the primary specification theorem: it gives both soundness and completeness
    of `validateConfig`. The forward direction uses the individual soundness theorems.
    The backward direction reconstructs the boolean from the propositions. -/
theorem validate_ok_iff (c : Config) :
    validateConfig c = true ↔
    (c.id ≠ 0 ∧ c.heartbeat_tick ≥ 1 ∧ c.election_tick > c.heartbeat_tick ∧
     c.minElectionTick ≥ c.election_tick ∧ c.minElectionTick < c.maxElectionTick ∧
     c.max_inflight_msgs ≥ 1 ∧
     (c.read_only_option = .LeaseBased → c.check_quorum = true) ∧
     c.max_uncommitted_size ≥ c.max_size_per_msg) := by
  constructor
  · intro h
    exact ⟨validate_id c h, validate_hb c h, validate_election_gt_hb c h,
           validate_min_election c h, validate_tick_range c h,
           validate_inflight c h, validate_lease c h, validate_uncommitted c h⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    simp only [validateConfig, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [c1, bne_iff_ne]; exact h1          -- C1: id ≠ 0
    · simp only [c2, bne_iff_ne]; omega              -- C2: heartbeat_tick ≥ 1 → ≠ 0
    · simp only [c3, decide_eq_true_eq]; exact h3   -- C3: election_tick > heartbeat_tick
    · simp only [c4, decide_eq_true_eq]; exact h4   -- C4: minElectionTick ≥ election_tick
    · simp only [c5, decide_eq_true_eq]; exact h5   -- C5: minElectionTick < maxElectionTick
    · simp only [c6, bne_iff_ne]; omega              -- C6: max_inflight_msgs ≥ 1 → ≠ 0
    · exact (c7_iff_implication c).mpr h7            -- C7: implication → bool
    · simp only [c8, decide_eq_true_eq]; exact h8   -- C8: max_uncommitted_size ≥ max_size_per_msg

/-! ## Default config validity -/

/-- Default config (matching `Config::default()` from Rust), with a given `id`. -/
def defaultConfig (id : Nat) : Config where
  id                   := id
  heartbeat_tick       := 2
  election_tick        := 20
  max_inflight_msgs    := 256
  max_uncommitted_size := 0xFFFFFFFFFFFFFFFF   -- NO_LIMIT approximation
  max_size_per_msg     := 0
  min_election_tick    := 0                    -- effective: use election_tick (= 20)
  max_election_tick    := 0                    -- effective: use 2 * election_tick (= 40)
  read_only_option     := .Safe
  check_quorum         := false

/-- The default config with `id = 0` fails validation (C1 fails). -/
theorem validate_default_id_zero :
    validateConfig (defaultConfig 0) = false := by decide

/-- Setting any `id ≠ 0` on the default config yields a valid configuration. -/
theorem validate_default_id_pos (id : Nat) (h : id ≠ 0) :
    validateConfig (defaultConfig id) = true := by
  rw [validate_ok_iff]
  simp only [defaultConfig, Config.minElectionTick, Config.maxElectionTick]
  -- All arithmetic constraints hold by omega; C7 holds vacuously (Safe ≠ LeaseBased)
  refine ⟨h, by omega, by omega, by omega, by omega, by omega, ?_, by omega⟩
  intro heq  -- heq : .Safe = .LeaseBased — this is a contradiction
  exact absurd heq (by decide)

/-! ## Derived properties -/

/-- If `validateConfig c = true`, then `election_tick ≥ 2`. -/
theorem validate_election_ge_2 (c : Config) (h : validateConfig c = true) :
    c.election_tick ≥ 2 := by
  have h2 := validate_hb c h
  have h3 := validate_election_gt_hb c h
  omega

/-- If `validateConfig c = true`, then `minElectionTick c ≥ 2`. -/
theorem validate_min_election_ge_2 (c : Config) (h : validateConfig c = true) :
    c.minElectionTick ≥ 2 := by
  have h_ge2 := validate_election_ge_2 c h
  have h4    := validate_min_election c h
  omega

/-- If `validateConfig c = true`, then `maxElectionTick c ≥ 3`. -/
theorem validate_max_election_ge_3 (c : Config) (h : validateConfig c = true) :
    c.maxElectionTick ≥ 3 := by
  have h_min := validate_min_election_ge_2 c h
  have h5    := validate_tick_range c h
  omega

/-- With default tick fields (`min = max = 0`), the effective range is `[election_tick, 2 * election_tick)`. -/
theorem validate_default_tick_range (c : Config) (h : validateConfig c = true)
    (hmin : c.min_election_tick = 0) (hmax : c.max_election_tick = 0) :
    c.minElectionTick = c.election_tick ∧ c.maxElectionTick = 2 * c.election_tick := by
  exact ⟨minElectionTick_default c hmin, maxElectionTick_default c hmax⟩

/-- With default tick fields, C5 reduces to `election_tick < 2 * election_tick`,
    i.e., `election_tick ≥ 1` (which is implied by C2 + C3). -/
theorem validate_default_c5_equiv (c : Config)
    (hmin : c.min_election_tick = 0) (hmax : c.max_election_tick = 0) :
    c5 c = true ↔ c.election_tick ≥ 1 := by
  simp only [c5, minElectionTick_default c hmin, maxElectionTick_default c hmax,
             decide_eq_true_eq]
  omega

/-- When `max_size_per_msg = 0`, C8 always holds. -/
theorem validate_c8_trivial (c : Config) (h : c.max_size_per_msg = 0) :
    c8 c = true := by
  simp [c8, h]

/-- `Safe` and `ReadIndex` read_only_option never violate C7. -/
theorem validate_c7_safe (c : Config) (h : c.read_only_option = .Safe) :
    c7 c = true := by
  simp [c7, h]

theorem validate_c7_read_index (c : Config) (h : c.read_only_option = .ReadIndex) :
    c7 c = true := by
  simp [c7, h]

/-- **Completeness of C7**: `c7 c = true` iff `read_only_option ≠ LeaseBased` or `check_quorum = true`. -/
theorem c7_iff (c : Config) :
    c7 c = true ↔ (c.read_only_option ≠ .LeaseBased ∨ c.check_quorum = true) := by
  unfold c7
  cases c.read_only_option
  · -- Safe: !(Safe == LeaseBased) || check = !false || check = true; always true
    simp
  · -- ReadIndex: !(ReadIndex == LeaseBased) || check = true; always true
    simp
  · -- LeaseBased: !(LeaseBased == LeaseBased) || check = false || check = check
    simp only [Bool.beq_self_eq_true, Bool.not_true, Bool.false_or]
    constructor
    · intro h; exact Or.inr h
    · intro h; rcases h with h | h
      · exact absurd rfl h
      · exact h

/-- Equivalent form: `c7 c = true ↔ c.read_only_option = LeaseBased → c.check_quorum = true`. -/
theorem c7_iff_implication (c : Config) :
    c7 c = true ↔ (c.read_only_option = .LeaseBased → c.check_quorum = true) := by
  rw [c7_iff]; tauto

end FVSquad.ConfigValidate
