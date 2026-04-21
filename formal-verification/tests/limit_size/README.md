# limit_size Correspondence Tests

> 🔬 *Lean Squad — Task 8 Route B correspondence tests.*

## What is validated

The `limit_size` function from `src/util.rs` truncates a list of entries so that the
cumulative size stays within a budget.  The key rule: the first entry is **always** kept.

The Lean model `limitSize` in `FVSquad/LimitSize.lean` abstracts entries as natural
numbers (each value IS its size, via `id : Nat → Nat`).

### Abstraction bridge

| Lean | Rust |
|------|------|
| `limitSize id sizes (some budget)` | `limit_size(&mut entries, Some(budget))` |
| `sizes[i] : Nat` (entry size value) | `entries[i].compute_size()` (proto encoded length) |
| `none` budget | `None` or `Some(u64::MAX)` |

For a prost `Entry` with only the `data` field set to `n` bytes:
`encoded_len() = 2 + n` (1-byte tag + 1-byte varint length + n bytes).
So `sizes[i] = 100` corresponds to `Entry { data: vec![0u8; 98] }`.

## Test commands

**Lean (static, at build time):**
```bash
cd formal-verification/lean
lake build FVSquad.LimitSizeCorrespondence
```

**Rust (runtime):**
```bash
cargo test test_limit_size_correspondence
```

## Cases (10 total)

| ID | sizes | budget | expected_len |
|----|-------|--------|-------------|
| 1  | [] | 100 | 0 |
| 2  | [100] | 0 | 1 |
| 3  | [100×5] | 500 | 5 |
| 4  | [100×5] | 400 | 4 |
| 5  | [100×5] | 220 | 2 |
| 6  | [100×5] | 100 | 1 |
| 7  | [100×5] | 0 | 1 |
| 8  | [200,100,100] | 350 | 2 |
| 9  | [200,100,100] | 200 | 1 |
| 10 | [100×3] | none | 3 |

## Result

Both sides agree on all 10 cases. Correspondence level: **Exact** for the
majority-quorum path. The size-function abstraction is clearly documented.
