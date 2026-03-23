# Informal Spec: `get_priority`

> Source: `src/raft.rs` (line ~302)
> Lean file: `formal-verification/lean/FVSquad/GetPriority.lean`
> Phase: 3 — Lean Spec

---

## Purpose

`get_priority(m: &Message) -> i64` returns the effective priority of a Raft
message. The function exists to maintain backward compatibility between two
versions of the priority field in the protobuf Message type:

- **New field** (`int64 priority = 16`, field tag 16): The preferred field.
  Non-zero when the sender supports priorities.
- **Deprecated field** (`uint64 deprecated_priority = 14`, field tag 14):
  Used by older nodes. A `u64` value that may not fit in `i64`.

---

## Preconditions

None — `get_priority` is total and handles all input combinations.

---

## Postconditions

| Case | Result |
|---|---|
| `m.priority ≠ 0` | `m.priority` (i64, returned as-is) |
| `m.priority = 0`, `m.deprecated_priority ≤ i64::MAX` | `m.deprecated_priority as i64` |
| `m.priority = 0`, `m.deprecated_priority > i64::MAX` | `i64::MAX` |

where `i64::MAX = 2^63 − 1 = 9_223_372_036_854_775_807`.

---

## Invariants

1. **Priority field dominates**: When `priority ≠ 0`, `deprecated_priority` is
   completely ignored. The two fields are mutually exclusive selectors.
2. **Overflow clamping**: When `deprecated_priority > INT64_MAX`, the function
   clamps to `INT64_MAX` rather than wrapping around or panicking.
3. **Zero means unknown**: Both fields zero ↔ effective priority is 0. This is
   the default state of a new `Message`.
4. **Non-negativity from deprecated**: When `priority = 0`, the result is always
   non-negative (since `deprecated_priority : u64`).
5. **No clamp on new field**: The `priority` field is returned as-is without
   bounds checking, even if negative or > INT64_MAX.

---

## Edge Cases

- **Both zero**: `get_priority` returns 0. Messages without explicit priority
  have effective priority 0 (equal weight in scheduling).
- **priority = INT64_MAX**: The result is INT64_MAX (priority branch taken, not the
  overflow branch — but the value happens to equal INT64_MAX).
- **deprecated_priority = INT64_MAX**: The result is INT64_MAX (fits in i64, so
  returned directly).
- **deprecated_priority = INT64_MAX + 1**: Overflows; clamped to INT64_MAX.
- **negative priority**: Allowed (i64 can be negative); returned as-is when ≠ 0.

---

## Examples

| `priority` | `deprecated_priority` | Result |
|---|---|---|
| 100 | 999 | 100 (new field wins) |
| 0 | 42 | 42 (deprecated fits) |
| 0 | 2^63 − 1 | 2^63 − 1 (deprecated = INT64_MAX, fits) |
| 0 | 2^63 | INT64_MAX (deprecated overflows, clamped) |
| 0 | 0 | 0 (default/no priority) |
| −5 | 999 | −5 (priority ≠ 0, used as-is) |

---

## Inferred Intent

The function exists because the protobuf field tag changed between versions.
Older nodes set `deprecated_priority` (u64); newer nodes set `priority` (i64).
The conversion logic ensures:

1. New nodes talking to old nodes: `priority ≠ 0`, so `deprecated_priority` ignored.
2. Old nodes talking to new nodes: `priority = 0` (default), so `deprecated_priority`
   is used via safe conversion.
3. The `i64::MAX` clamp prevents UB-equivalent behavior in the type conversion.

---

## Open Questions

1. Can `priority` legitimately be negative? The type is `i64` which allows it,
   and the function would return the negative value. Is negative priority meaningful?
2. Is there a canonical "no priority" sentinel, or is 0 used for that? The code
   treats 0 as "no new priority set", which means 0 is not a valid priority value
   in the new field.
3. Are there additional invariants maintained by callers (e.g., `priority` is set
   iff the node version supports it)?

---

*🔬 Lean Squad — automated formal verification.*
