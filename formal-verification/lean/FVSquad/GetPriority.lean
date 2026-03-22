/-!
# Message Priority Selection — Lean 4 Specification

Formal specification of `get_priority` from `src/raft.rs` (line ~302):

```rust
fn get_priority(m: &Message) -> i64 {
    if m.priority != 0 {
        m.priority
    } else {
        i64::try_from(m.deprecated_priority).unwrap_or(i64::MAX)
    }
}
```

The function selects the effective message priority:
- If `priority` (i64, field 16) is non-zero, use it directly.
- Otherwise, convert `deprecated_priority` (u64, field 14) to i64.
  Values exceeding `i64::MAX` (= 2^63 − 1) are clamped to `i64::MAX`.

## Context

`priority` (i64) supersedes `deprecated_priority` (u64). The two fields are a
backward-compatibility mechanism: new nodes set `priority`; old nodes set
`deprecated_priority`. The u64 → i64 conversion clamps on overflow.

## Model scope and approximations

* **`Int`** models Rust's `i64` (unbounded; overflow not modelled since the clamp
  is explicit in the function body).
* **`Nat`** models Rust's `u64` (unbounded; clamping handles large values).
* **Omitted**: the full `Message` struct; only the two priority fields are modelled.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Tactic

namespace FVSquad.GetPriority

/-! ## Constants and types -/

/-- The maximum value of Rust's `i64`: 2^63 − 1. -/
def INT64_MAX : Int := 2^63 - 1

/-- Simplified message type carrying only the two priority fields. -/
structure Msg where
  /-- New priority field (`int64 priority = 16`). Non-zero means "use this". -/
  priority            : Int
  /-- Deprecated priority field (`uint64 deprecated_priority = 14`). -/
  deprecated_priority : Nat
  deriving Repr

/-! ## Implementation model -/

/-- `get_priority`: returns `m.priority` if non-zero, otherwise converts
    `m.deprecated_priority` (u64) to i64 with a clamp to `INT64_MAX`. -/
def getPriority (m : Msg) : Int :=
  if m.priority ≠ 0 then
    m.priority
  else if (m.deprecated_priority : Int) ≤ INT64_MAX then
    (m.deprecated_priority : Int)
  else
    INT64_MAX

/-! ## Key lemma: INT64_MAX is positive -/

private lemma INT64_MAX_pos : (0 : Int) < INT64_MAX := by
  simp [INT64_MAX]; norm_num

/-! ## Propositions -/

/-- PROP-1  When `priority ≠ 0`, the new field is returned unchanged. -/
theorem getPriority_nonzero (m : Msg) (h : m.priority ≠ 0) :
    getPriority m = m.priority := by
  simp [getPriority, h]

/-- PROP-2  When `priority = 0` and `deprecated_priority` fits in i64,
    the deprecated field is returned (cast to Int). -/
theorem getPriority_deprecated_fits (m : Msg) (h0 : m.priority = 0)
    (hfit : (m.deprecated_priority : Int) ≤ INT64_MAX) :
    getPriority m = (m.deprecated_priority : Int) := by
  simp [getPriority, h0, hfit]

/-- PROP-3  When `priority = 0` and `deprecated_priority` overflows i64,
    `INT64_MAX` is returned (the clamp). -/
theorem getPriority_deprecated_overflow (m : Msg) (h0 : m.priority = 0)
    (hover : ¬ (m.deprecated_priority : Int) ≤ INT64_MAX) :
    getPriority m = INT64_MAX := by
  simp [getPriority, h0, hover]

/-- PROP-4  Both fields zero → result is zero. -/
theorem getPriority_both_zero (m : Msg) (h0 : m.priority = 0)
    (hdep : m.deprecated_priority = 0) :
    getPriority m = 0 := by
  simp [getPriority, h0, hdep]

/-- PROP-5  The `priority` branch takes precedence: if `priority ≠ 0`,
    `deprecated_priority` is completely ignored regardless of its value. -/
theorem getPriority_ignores_deprecated_when_priority_nonzero
    (m₁ m₂ : Msg) (hpri : m₁.priority = m₂.priority) (hne : m₁.priority ≠ 0) :
    getPriority m₁ = getPriority m₂ := by
  simp [getPriority, hne, hpri]

/-- PROP-6  If `priority` overflows (> INT64_MAX) in the new field, the result
    is exactly that value (no clamping of the `priority` field itself). -/
theorem getPriority_no_clamp_priority (m : Msg) (h : m.priority > INT64_MAX) :
    getPriority m = m.priority := by
  apply getPriority_nonzero
  intro h0
  rw [h0] at h
  exact absurd h (by linarith [INT64_MAX_pos])

/-- PROP-7  When `priority = 0`, the result is non-negative
    (since `deprecated_priority : Nat` is cast to a non-negative Int). -/
theorem getPriority_nonneg_when_zero (m : Msg) (h0 : m.priority = 0) :
    0 ≤ getPriority m := by
  simp only [getPriority, h0, ne_eq, not_true, not_false_eq_true, ite_false]
  split_ifs with h
  · exact Int.ofNat_nonneg m.deprecated_priority
  · linarith [INT64_MAX_pos]

/-- PROP-8  The result is bounded above by `INT64_MAX` when
    `priority ≤ INT64_MAX` (the common case for well-behaved priorities). -/
theorem getPriority_le_max (m : Msg) (hbound : m.priority ≤ INT64_MAX) :
    getPriority m ≤ INT64_MAX := by
  unfold getPriority
  split_ifs with h1 h2
  · exact hbound
  · exact h2
  · exact le_refl _

/-- PROP-9  Result is zero iff both fields are zero.

    (←): trivially follows from PROP-4.
    (→): if `priority ≠ 0`, result = priority ≠ 0; if `priority = 0` and
    `deprecated_priority ≠ 0`, result ≥ 0 but equals deprecated or INT64_MAX > 0. -/
theorem getPriority_zero_iff (m : Msg) :
    getPriority m = 0 ↔ m.priority = 0 ∧ m.deprecated_priority = 0 := by
  constructor
  · intro h
    unfold getPriority at h
    split_ifs at h with h1 h2
    · exact absurd h (by omega)
    · exact ⟨by push_neg at h1; exact h1, by exact_mod_cast h⟩
    · exact absurd h (by linarith [INT64_MAX_pos])
  · rintro ⟨h0, hdep⟩
    exact getPriority_both_zero m h0 hdep

/-- PROP-10  When `priority = 0`, the result is the deprecated field clamped to
    `INT64_MAX`. Equivalently, `min (deprecated_priority : Int) INT64_MAX`. -/
theorem getPriority_zero_eq_clamp (m : Msg) (h0 : m.priority = 0) :
    getPriority m = min (m.deprecated_priority : Int) INT64_MAX := by
  simp only [getPriority, h0, ne_eq, not_true, not_false_eq_true, ite_false]
  split_ifs with h
  · simp [min_def, h]
  · push_neg at h
    simp [min_def, le_of_lt (lt_of_not_le h)]

/-! ## Examples -/

-- Non-zero priority takes precedence
#eval getPriority ⟨100, 999⟩      -- 100 (new field wins)

-- Zero priority, deprecated fits in i64
#eval getPriority ⟨0, 42⟩          -- 42 (deprecated fits)

-- Zero priority, deprecated overflows i64 (2^64 > 2^63-1)
#eval getPriority ⟨0, 2^64⟩        -- 9223372036854775807 (INT64_MAX, clamped)

-- Both zero: default / no priority
#eval getPriority ⟨0, 0⟩           -- 0

end FVSquad.GetPriority
