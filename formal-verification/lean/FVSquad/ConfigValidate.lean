/-!
# Formal Specification: `Config::validate`

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

This file formalises `Config::validate` from `src/config.rs`.

## What `Config::validate` does

```rust
pub fn validate(&self) -> Result<()>
```

Checks that the Raft configuration is well-formed. Returns `Ok(())` iff all
eight independent arithmetic/boolean constraints hold. Returns `Err(ConfigInvalid(…))`
on the first violated constraint.

## Modelling choices

- The full `Config` struct is abstracted to a record containing only the fields
  relevant to `validate`.  Boolean fields (`check_quorum`, `batch_append`, …)
  that are not checked by `validate` are omitted.
- `u64`/`usize` fields are modelled as `Nat` (unbounded, no overflow).
- `ReadOnlyOption` has two relevant values: `Safe` (default) and `LeaseBased`.
- `INVALID_ID = 0`.
- The two accessor helpers (`min_election_tick()`, `max_election_tick()`) are
  inlined as pure functions.
- The Rust `Result<()>` is modelled as `Bool` (`true` = Ok, `false` = Err).
-/

/-! ## ReadOnlyOption -/

inductive ReadOnlyOption where
  | Safe
  | LeaseBased
  deriving DecidableEq, Repr

/-! ## Config record -/

structure Config where
  id                 : Nat   -- u64; must be ≠ 0 (INVALID_ID = 0)
  heartbeat_tick     : Nat   -- usize; must be > 0
  election_tick      : Nat   -- usize; must be > heartbeat_tick
  min_election_tick  : Nat   -- usize; 0 means "use election_tick"
  max_election_tick  : Nat   -- usize; 0 means "use 2 * election_tick"
  max_inflight_msgs  : Nat   -- usize; must be > 0
  check_quorum       : Bool
  read_only_option   : ReadOnlyOption
  max_size_per_msg   : Nat   -- u64
  max_uncommitted_size : Nat -- u64; must be ≥ max_size_per_msg
  deriving Repr

/-! ## Accessor helpers (mirror Rust methods) -/

/-- Canonical lower bound of the randomised election timeout.
    Mirrors `Config::min_election_tick()` in `src/config.rs`. -/
def Config.minTick (c : Config) : Nat :=
  if c.min_election_tick == 0 then c.election_tick else c.min_election_tick

/-- Canonical upper bound (exclusive) of the randomised election timeout.
    Mirrors `Config::max_election_tick()` in `src/config.rs`. -/
def Config.maxTick (c : Config) : Nat :=
  if c.max_election_tick == 0 then 2 * c.election_tick else c.max_election_tick

/-! ## Individual constraint predicates -/

/-- C1: node id must be non-zero. -/
def Config.validId (c : Config) : Prop := c.id ≠ 0

/-- C2: heartbeat tick must be positive. -/
def Config.validHeartbeat (c : Config) : Prop := c.heartbeat_tick > 0

/-- C3: election tick must strictly exceed heartbeat tick. -/
def Config.validElection (c : Config) : Prop := c.election_tick > c.heartbeat_tick

/-- C4: canonical min timeout must be ≥ election_tick. -/
def Config.validMinTick (c : Config) : Prop := c.minTick ≥ c.election_tick

/-- C5: the timeout range must be non-trivial (min < max). -/
def Config.validTickRange (c : Config) : Prop := c.minTick < c.maxTick

/-- C6: max inflight messages must be positive. -/
def Config.validInflight (c : Config) : Prop := c.max_inflight_msgs > 0

/-- C7: LeaseBased read mode requires check_quorum. -/
def Config.validReadOnly (c : Config) : Prop :=
  c.read_only_option = ReadOnlyOption.LeaseBased → c.check_quorum = true

/-- C8: max_uncommitted_size must be ≥ max_size_per_msg. -/
def Config.validUncommitted (c : Config) : Prop :=
  c.max_uncommitted_size ≥ c.max_size_per_msg

/-! ## The complete validity predicate -/

/-- A `Config` is valid iff all eight constraints hold. -/
def Config.valid (c : Config) : Prop :=
  c.validId ∧ c.validHeartbeat ∧ c.validElection ∧ c.validMinTick ∧
  c.validTickRange ∧ c.validInflight ∧ c.validReadOnly ∧ c.validUncommitted

/-! ## Boolean decision procedure -/

/-- Decidable boolean version of `validate`. Returns `true` iff valid.
    This directly models `Config::validate` returning `Ok(())`. -/
def configValidate (c : Config) : Bool :=
  c.id ≠ 0 &&
  c.heartbeat_tick > 0 &&
  c.election_tick > c.heartbeat_tick &&
  c.minTick ≥ c.election_tick &&
  c.minTick < c.maxTick &&
  c.max_inflight_msgs > 0 &&
  (c.read_only_option ≠ ReadOnlyOption.LeaseBased || c.check_quorum) &&
  c.max_uncommitted_size ≥ c.max_size_per_msg

/-! ## Evaluations (sanity-check against src/config.rs examples) -/

section Eval

-- Default-like config with id=1 (should pass)
private def defaultCfg : Config :=
  { id := 1, heartbeat_tick := 2, election_tick := 20,
    min_election_tick := 0, max_election_tick := 0,
    max_inflight_msgs := 256, check_quorum := false,
    read_only_option := ReadOnlyOption.Safe,
    max_size_per_msg := 0, max_uncommitted_size := UInt64.size }

#eval configValidate defaultCfg           -- expected: true

-- id = 0: invalid
#eval configValidate { defaultCfg with id := 0 }           -- expected: false

-- heartbeat_tick = 0: invalid
#eval configValidate { defaultCfg with heartbeat_tick := 0 } -- expected: false

-- election_tick ≤ heartbeat_tick: invalid
#eval configValidate { defaultCfg with election_tick := 2 }  -- expected: false

-- min_election_tick = election_tick - 1: invalid
#eval configValidate { defaultCfg with min_election_tick := 19 } -- expected: false

-- min = max election tick: invalid
#eval configValidate { defaultCfg with min_election_tick := 20, max_election_tick := 20 } -- expected: false

-- min < max election tick: valid
#eval configValidate { defaultCfg with min_election_tick := 20, max_election_tick := 21 } -- expected: true

-- LeaseBased without check_quorum: invalid
#eval configValidate { defaultCfg with read_only_option := ReadOnlyOption.LeaseBased } -- expected: false

-- LeaseBased with check_quorum: valid
#eval configValidate { defaultCfg with read_only_option := ReadOnlyOption.LeaseBased, check_quorum := true } -- expected: true

-- max_uncommitted < max_size_per_msg: invalid
#eval configValidate { defaultCfg with max_uncommitted_size := 0, max_size_per_msg := 100 } -- expected: false

end Eval

/-! ## Key theorems -/

/-- T1: `configValidate` correctly reflects `Config.valid`.
    The boolean procedure is equivalent to the propositional predicate. -/
theorem configValidate_iff_valid (c : Config) :
    configValidate c = true ↔ Config.valid c := by
  simp only [Config.valid, Config.validId, Config.validHeartbeat, Config.validElection,
    Config.validMinTick, Config.validTickRange, Config.validInflight,
    Config.validReadOnly, Config.validUncommitted]
  constructor
  · intro h
    simp only [configValidate, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3,
           of_decide_eq_true h4, of_decide_eq_true h5, of_decide_eq_true h6,
           fun hleased => h7.elim (fun hne => absurd hleased (of_decide_eq_true hne)) id,
           of_decide_eq_true h8⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    simp only [configValidate, Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨decide_eq_true h1, decide_eq_true h2⟩, decide_eq_true h3⟩,
           decide_eq_true h4⟩, decide_eq_true h5⟩, decide_eq_true h6⟩, ?_⟩, decide_eq_true h8⟩
    cases h_ro : c.read_only_option
    · exact Or.inl (decide_eq_true (by decide))
    · exact Or.inr (h7 h_ro)

/-- T2: The default config with a valid id is valid.
    Verifies that `Config::new(1)` (using all defaults) passes validation. -/
theorem defaultCfg_valid : configValidate defaultCfg = true := by native_decide

/-- T3: Config with id = 0 is always invalid. -/
theorem zero_id_invalid (c : Config) (h : c.id = 0) : configValidate c = false := by
  cases hb : configValidate c with
  | false => rfl
  | true =>
    simp only [configValidate, Bool.and_eq_true] at hb
    exact absurd h (of_decide_eq_true hb.1.1.1.1.1.1.1)

/-- T4: If heartbeat_tick = 0, config is invalid. -/
theorem zero_heartbeat_invalid (c : Config) (h : c.heartbeat_tick = 0) :
    configValidate c = false := by
  cases hb : configValidate c with
  | false => rfl
  | true =>
    simp only [configValidate, Bool.and_eq_true] at hb
    exact absurd (of_decide_eq_true hb.1.1.1.1.1.1.2) (by omega)

/-- T5: election_tick must strictly exceed heartbeat_tick. -/
theorem election_le_heartbeat_invalid (c : Config)
    (h : c.election_tick ≤ c.heartbeat_tick) : configValidate c = false := by
  cases hb : configValidate c with
  | false => rfl
  | true =>
    simp only [configValidate, Bool.and_eq_true] at hb
    exact absurd (of_decide_eq_true hb.1.1.1.1.1.2) (by omega)

/-- T6: LeaseBased without check_quorum is invalid. -/
theorem lease_without_quorum_invalid (c : Config)
    (hro : c.read_only_option = ReadOnlyOption.LeaseBased)
    (hcq : c.check_quorum = false) : configValidate c = false := by
  cases hb : configValidate c with
  | false => rfl
  | true =>
    simp only [configValidate, Bool.and_eq_true, Bool.or_eq_true] at hb
    obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, h7⟩, _⟩ := hb
    rcases h7 with hne | hcq'
    · exact absurd hro (of_decide_eq_true hne)
    · exact absurd hcq' (by rw [hcq]; decide)

/-- T7: If max_uncommitted_size < max_size_per_msg, config is invalid. -/
theorem uncommitted_less_than_msg_invalid (c : Config)
    (h : c.max_uncommitted_size < c.max_size_per_msg) : configValidate c = false := by
  cases hb : configValidate c with
  | false => rfl
  | true =>
    simp only [configValidate, Bool.and_eq_true] at hb
    exact absurd (of_decide_eq_true hb.2) (by omega)

/-- T8: min_timeout must be ≥ election_tick when min_election_tick is explicitly set. -/
theorem explicit_min_below_election_invalid (c : Config)
    (hne : c.min_election_tick ≠ 0)
    (hlt : c.min_election_tick < c.election_tick) : configValidate c = false := by
  cases hb : configValidate c with
  | false => rfl
  | true =>
    simp only [configValidate, Bool.and_eq_true] at hb
    have h4 := of_decide_eq_true hb.1.1.1.1.2
    simp only [Config.minTick] at h4
    cases hif : c.min_election_tick == 0 with
    | false => simp [hif] at h4; exact absurd h4 (by omega)
    | true  => simp only [beq_iff_eq] at hif; exact absurd hif hne

/-- T9: Validity is monotone — adding extra inflight capacity cannot break a valid config. -/
theorem valid_inflight_increase (c : Config) (n : Nat)
    (hv : configValidate c = true)
    (hge : n ≥ c.max_inflight_msgs) :
    configValidate { c with max_inflight_msgs := n } = true := by
  simp only [configValidate, Bool.and_eq_true, Bool.or_eq_true] at hv ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hv
  refine ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, ?_⟩, h7⟩, h8⟩
  exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h6) hge)

/-- T10: configValidate returns false iff ¬ Config.valid c. -/
theorem configValidate_false_iff_invalid (c : Config) :
    configValidate c = false ↔ ¬ Config.valid c := by
  constructor
  · intro h hv
    have := (configValidate_iff_valid c).mpr hv
    simp_all
  · intro h
    cases hb : configValidate c with
    | false => rfl
    | true => exact absurd ((configValidate_iff_valid c).mp hb) h
