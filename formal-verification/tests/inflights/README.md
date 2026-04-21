# inflights Correspondence Tests

> 🔬 *Lean Squad — Task 8 Route B correspondence tests.*

## What is validated

`Inflights` operations from `src/tracker/inflights.rs`. The Lean model in
`FVSquad/Inflights.lean` abstracts the ring-buffer as a simple `List Nat` queue.

## Abstraction

| Lean | Rust |
|------|------|
| `{ queue : List Nat, cap : Nat }` | Ring buffer with `start`, `count`, `buffer`, `cap` |
| `queue` (in order) | Logical content: `buffer[start..start+count]` (modulo wrap) |
| `Inflights.add x` | `inflights.add(x)` |
| `Inflights.freeTo to` | `inflights.free_to(to)` |
| `Inflights.freeFirstOne` | `inflights.free_first_one()` |
| `Inflights.reset` | `inflights.reset()` |
| `Inflights.full` | `inflights.full()` |
| `Inflights.count` | `inflights.count()` |

## Test commands

**Lean (static, at build time):**
```bash
cd formal-verification/lean
lake build FVSquad.InflightsCorrespondence
```

**Rust (runtime):**
```bash
cargo test test_inflights_correspondence
```

## Cases (12 total)

| ID | Operations | Check | Expected |
|----|-----------|-------|---------|
| 1  | new(3) | count | 0 |
| 2  | new(3) | full | false |
| 3  | new(3).add(10) | queue | [10] |
| 4  | new(3).add(10).add(20) | count | 2 |
| 5  | new(3).add(10).add(20).add(30) | full | true |
| 6  | new(3).add(10).add(20).freeTo(10) | queue | [20] |
| 7  | new(3).add(10).add(20).add(30).freeTo(20) | queue | [30] |
| 8  | new(3).add(10).add(20).freeTo(25) | queue | [] |
| 9  | new(3).add(10).add(20).freeFirstOne | queue | [20] |
| 10 | new(3).add(10).add(20).reset | queue | [] |
| 11 | new(3).add(10).reset | full | false |
| 12 | new(1).add(10) | full | true |

## Result

Both sides agree on all 12 cases. Correspondence level: **Exact** (the Lean model's
`queue` equals the Rust ring buffer's logical content in traversal order).
