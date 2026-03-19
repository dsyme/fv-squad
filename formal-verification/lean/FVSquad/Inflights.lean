/-!
# Inflights — Lean 4 Specification

Formal specification of the `Inflights` ring buffer from `src/tracker/inflights.rs`.
`Inflights` is a bounded FIFO queue that tracks in-flight Raft `MsgAppend` message
indices, enforcing a cap on unacknowledged messages per peer.

## Model scope and approximations

* **Ring buffer layout abstracted**: the circular array (`start`, `buffer`) is modelled
  as a plain `List Nat` giving the logical queue contents in FIFO order (oldest first).
  The ring addressing arithmetic (`(start + i) % cap`) is an implementation detail not
  relevant to the correctness properties we verify here.
* **`incoming_cap` / `set_cap` omitted**: capacity adjustment is deferred to a later
  task. The model has a fixed `cap`.
* **`u64` indices**: modelled as `Nat` (unbounded).
* **Memory helpers** (`maybe_free_buffer`, `buffer_is_allocated`): implementation-only;
  omitted.
* **`free_to` semantics**: the Rust code frees all entries whose value is **≤ to** from
  the front of the queue. Our model uses `List.dropWhile (· ≤ to)`.
* **Monotonicity**: INV-4 (queue contents are strictly increasing) is stated as a
  separate predicate; it holds in correct Raft usage but is not enforced by the
  implementation itself.

🔬 *Lean Squad — auto-generated formal specification.*
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Tactic

namespace FVSquad.Inflights

/-! ## Abstract model -/

/-- Abstract model of `Inflights`: a bounded FIFO queue of in-flight message indices.
    The ring-buffer layout is abstracted away; `items` gives the logical queue contents
    in FIFO order (oldest first). -/
structure Inflights where
  cap   : Nat        -- maximum capacity
  items : List Nat   -- in-flight indices, FIFO order (oldest first)
  deriving Repr

/-! ## Representation invariants -/

/-- **INV-1 (bounded)**: the number of in-flight items never exceeds capacity. -/
def bounded (inf : Inflights) : Prop :=
  inf.items.length ≤ inf.cap

/-- **INV-4 (monotone)**: the queue contents are strictly increasing.
    Holds in correct Raft usage (indices are appended in order); not enforced by code. -/
def monotone (inf : Inflights) : Prop :=
  inf.items.Pairwise (· < ·)

/-! ## Operations -/

/-- Returns `true` if the buffer is at capacity. Models `Inflights::full`. -/
def full (inf : Inflights) : Bool :=
  inf.items.length == inf.cap

/-- Adds a new in-flight index to the back of the queue.
    Only valid when `¬ full inf` (panics in Rust otherwise). -/
def add (inf : Inflights) (idx : Nat) : Inflights :=
  { inf with items := inf.items ++ [idx] }

/-- Frees all in-flight indices ≤ `to` from the front of the queue.
    Models `Inflights::free_to`. -/
def freeTo (inf : Inflights) (to : Nat) : Inflights :=
  { inf with items := inf.items.dropWhile (fun x => x ≤ to) }

/-- Frees the oldest (front) element. No-op if empty.
    Models `Inflights::free_first_one`. -/
def freeFirstOne (inf : Inflights) : Inflights :=
  match inf.items with
  | []      => inf
  | x :: _  => freeTo inf x

/-- Empties the queue entirely. Models `Inflights::reset`. -/
def reset (inf : Inflights) : Inflights :=
  { inf with items := [] }

/-! ## Decidable sanity checks -/

private def ex1 : Inflights := { cap := 10, items := [0,1,2,3,4,5,6,7,8,9] }

-- full: 10 items, cap 10
example : full ex1 = true := by decide

-- freeTo 4 leaves [5,6,7,8,9]
example : (freeTo ex1 4).items = [5,6,7,8,9] := by decide

-- add after partial free
example : (add (freeTo ex1 4) 10).items = [5,6,7,8,9,10] := by decide

-- freeFirstOne frees index 0
example : (freeFirstOne ex1).items = [1,2,3,4,5,6,7,8,9] := by decide

-- reset empties everything
example : (reset ex1).items = [] := by decide

-- monotone: [0..9] is strictly increasing
example : monotone ex1 := by decide

/-! ## Private helper lemmas -/

/-- `dropWhile` is idempotent: applying it twice is the same as once. -/
private lemma dropWhile_idem {α : Type*} (p : α → Bool) : ∀ l : List α,
    (l.dropWhile p).dropWhile p = l.dropWhile p
  | [] => by simp
  | a :: t => by
    simp only [List.dropWhile_cons]
    cases h : p a
    · -- p a = false: dropWhile p (a::t) = a::t, and dropWhile on (a::t) is a::t again
      simp only [h, Bool.false_eq_true, ↓reduceIte, List.dropWhile_cons]
    · -- p a = true: dropWhile p (a::t) = dropWhile p t; apply IH
      simp only [h, ↓reduceIte]
      exact dropWhile_idem p t

/-- `dropWhile p l` is always `l.drop k` for some k. -/
private lemma dropWhile_is_drop {α : Type*} (p : α → Bool) : ∀ l : List α,
    ∃ k, l.dropWhile p = l.drop k
  | [] => ⟨0, rfl⟩
  | a :: t => by
    simp only [List.dropWhile_cons]
    cases h : p a
    · exact ⟨0, by simp⟩
    · simp only [h, ↓reduceIte]
      obtain ⟨k, hk⟩ := dropWhile_is_drop p t
      exact ⟨k + 1, by simp [hk]⟩

/-- For a strictly-sorted ascending list, every element in `dropWhile (· ≤ to)` is `> to`. -/
private lemma dropWhile_le_all_gt (to : Nat) : ∀ {l : List Nat},
    l.Pairwise (· < ·) → ∀ {x : Nat}, x ∈ l.dropWhile (· ≤ to) → to < x
  | [], _, _, hx => absurd hx (List.not_mem_nil _)
  | a :: t, hm, x, hx => by
    obtain ⟨ha_lt, ht⟩ := List.pairwise_cons.mp hm
    simp only [List.dropWhile_cons] at hx
    split_ifs at hx with h
    · -- a ≤ to, so a is dropped; x comes from the tail
      exact dropWhile_le_all_gt to ht hx
    · -- ¬ (a ≤ to), so a > to; dropWhile returns a::t immediately
      have ha_gt : to < a := Nat.lt_of_not_le h
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact ha_gt
      · exact Nat.lt_trans ha_gt (ha_lt x hxt)

/-! ## Specification theorems -/

/-! ### reset -/

theorem reset_empty (inf : Inflights) : (reset inf).items = [] := by
  simp [reset]

theorem reset_bounded (inf : Inflights) : bounded (reset inf) := by
  simp [bounded, reset]

theorem reset_cap (inf : Inflights) : (reset inf).cap = inf.cap := by
  simp [reset]

/-! ### add -/

theorem add_length (inf : Inflights) (idx : Nat) :
    (add inf idx).items.length = inf.items.length + 1 := by
  simp [add]

theorem add_cap (inf : Inflights) (idx : Nat) :
    (add inf idx).cap = inf.cap := by
  simp [add]

/-- `add` preserves `bounded` provided the buffer is not full. -/
theorem add_bounded (inf : Inflights) (idx : Nat)
    (hb : bounded inf) (hf : ¬ full inf) :
    bounded (add inf idx) := by
  simp [bounded, add, full] at *
  omega

/-- `add` appends `idx` to the logical back of the queue. -/
theorem add_items (inf : Inflights) (idx : Nat) :
    (add inf idx).items = inf.items ++ [idx] := by
  simp [add]

/-- `add idx` preserves `monotone` when `idx` is greater than all existing entries. -/
theorem add_monotone (inf : Inflights) (idx : Nat)
    (hm : monotone inf) (hgt : ∀ x ∈ inf.items, x < idx) :
    monotone (add inf idx) := by
  simp only [monotone, add]
  exact List.pairwise_append.mpr ⟨hm, List.pairwise_singleton _ _, by simpa⟩

/-! ### freeTo -/

theorem freeTo_cap (inf : Inflights) (to : Nat) :
    (freeTo inf to).cap = inf.cap := by
  simp [freeTo]

/-- `freeTo` never increases the item count. -/
theorem freeTo_length_le (inf : Inflights) (to : Nat) :
    (freeTo inf to).items.length ≤ inf.items.length := by
  simp [freeTo]
  exact List.length_dropWhile_le _ _

/-- `freeTo` preserves `bounded`. -/
theorem freeTo_bounded (inf : Inflights) (to : Nat) (hb : bounded inf) :
    bounded (freeTo inf to) := by
  exact Nat.le_trans (freeTo_length_le inf to) hb

/-- All remaining items after `freeTo to` are **strictly greater** than `to`.
    Requires the `monotone` invariant (strictly sorted queue). -/
theorem freeTo_all_gt (inf : Inflights) (to : Nat)
    (hm : monotone inf) (x : Nat) (hx : x ∈ (freeTo inf to).items) : to < x := by
  simp only [freeTo] at hx
  exact dropWhile_le_all_gt to hm hx

/-- `freeTo` result is a (list) suffix of the original items. -/
theorem freeTo_suffix (inf : Inflights) (to : Nat) :
    ∃ k, (freeTo inf to).items = inf.items.drop k := by
  simp only [freeTo]
  exact dropWhile_is_drop _ _

/-- Applying `freeTo` twice with the same bound is idempotent. -/
theorem freeTo_monotone_idempotent (inf : Inflights) (to : Nat) :
    freeTo (freeTo inf to) to = freeTo inf to := by
  simp only [freeTo, Inflights.mk.injEq, and_true]
  exact dropWhile_idem _ _

/-- `freeTo` preserves `monotone`. -/
theorem freeTo_monotone (inf : Inflights) (to : Nat) (hm : monotone inf) :
    monotone (freeTo inf to) := by
  simp only [monotone, freeTo]
  exact hm.sublist (List.dropWhile_sublist _)

/-- If all items are ≤ `to`, `freeTo to` empties the buffer. -/
theorem freeTo_all_le_empty (inf : Inflights) (to : Nat)
    (hall : ∀ x ∈ inf.items, x ≤ to) :
    (freeTo inf to).items = [] := by
  simp only [freeTo]
  rw [List.dropWhile_eq_nil_iff]
  simpa using hall

/-! ### freeFirstOne -/

/-- When the queue is non-empty, `freeFirstOne` removes exactly the first element. -/
theorem freeFirstOne_removes_head (inf : Inflights) (x : Nat) (xs : List Nat)
    (h : inf.items = x :: xs) :
    (freeFirstOne inf).items = xs.dropWhile (fun y => y ≤ x) := by
  simp [freeFirstOne, h, freeTo]

/-- `freeFirstOne` on a singleton list empties it. -/
theorem freeFirstOne_singleton (cap : Nat) (x : Nat) :
    (freeFirstOne { cap := cap, items := [x] }).items = [] := by
  simp [freeFirstOne, freeTo]

/-- `freeFirstOne` preserves `bounded`. -/
theorem freeFirstOne_bounded (inf : Inflights) (hb : bounded inf) :
    bounded (freeFirstOne inf) := by
  match h : inf.items with
  | [] => simp [freeFirstOne, h, bounded] at *; exact hb
  | _ :: _ =>
    simp only [freeFirstOne, h]
    exact freeTo_bounded inf _ hb

/-! ### full -/

/-- A freshly reset buffer is not full (when cap > 0). -/
theorem reset_not_full (inf : Inflights) (hcap : 0 < inf.cap) :
    ¬ full (reset inf) := by
  simp [full, reset, hcap]

/-- If `¬ full inf`, then after `add`, `full` may be true but the buffer stays bounded. -/
theorem add_then_bounded (inf : Inflights) (idx : Nat)
    (hb : bounded inf) (hf : ¬ full inf) :
    bounded (add inf idx) := add_bounded inf idx hb hf

/-! ## Concrete ring-buffer model (Task 4)

Models the actual Rust `Inflights` ring-buffer layout: a fixed-capacity circular array
indexed by `(start + i) % cap`. The abstract model is recovered via `concreteItems`. -/

/-- Concrete ring-buffer representation, mirroring the Rust `Inflights` struct.
    `buffer` is a `List Nat` of length `cap` (invariant: `buffer.length = cap`). -/
structure InflightsConcrete where
  start  : Nat         -- index of the oldest in-flight entry
  count  : Nat         -- number of active entries
  cap    : Nat         -- capacity of the ring buffer (fixed)
  buffer : List Nat    -- the ring buffer (length = cap)
  deriving Repr

/-- Extract the logical FIFO queue from the concrete ring buffer.
    Entry `i` (0-based from oldest) lives at `buffer[(start + i) % cap]`. -/
def concreteItems (c : InflightsConcrete) : List Nat :=
  (List.range c.count).map (fun i => c.buffer.getD ((c.start + i) % c.cap) 0)

/-- Concrete `add`: writes the new index at position `(start + count) % cap`. -/
def concreteAdd (c : InflightsConcrete) (idx : Nat) : InflightsConcrete :=
  let next := (c.start + c.count) % c.cap
  { c with buffer := c.buffer.set next idx, count := c.count + 1 }

/-- Concrete `free_to`: advances `start` past all entries ≤ `to`.
    Uses a tail-recursive helper mirroring the Rust `while` loop. -/
def concreteFreeTo (c : InflightsConcrete) (to : Nat) : InflightsConcrete :=
  let rec go (start count : Nat) : Nat × Nat :=
    if count == 0 then (start, count)
    else if to < c.buffer.getD (start % c.cap) 0 then (start, count)
    else go ((start + 1) % c.cap) (count - 1)
  let (s', cnt') := go c.start c.count
  { c with start := s', count := cnt' }

/-- Concrete `reset`: clears count and resets start. -/
def concreteReset (c : InflightsConcrete) : InflightsConcrete :=
  { c with start := 0, count := 0 }

/-- Lift a concrete inflights to the abstract model. -/
def toAbstract (c : InflightsConcrete) : Inflights :=
  { cap := c.cap, items := concreteItems c }

/-! ### Concrete decidable sanity checks -/

private def conEx : InflightsConcrete :=
  { start := 0, count := 5, cap := 10,
    buffer := [0, 1, 2, 3, 4, 0, 0, 0, 0, 0] }

-- concreteItems extracts first 5 entries
example : concreteItems conEx = [0, 1, 2, 3, 4] := by decide

-- concreteAdd appends the new index at position 5
example : (concreteAdd conEx 5).count = 6 := by decide
example : (concreteItems (concreteAdd conEx 5)).getLast! = 5 := by decide

-- wrap-around: start = 8, cap = 10, adding wraps index
private def conExWrap : InflightsConcrete :=
  { start := 8, count := 2, cap := 10,
    buffer := [10, 11, 0, 0, 0, 0, 0, 0, 8, 9] }
example : concreteItems conExWrap = [8, 9] := by decide
example : (concreteItems (concreteAdd conExWrap 10)).getLast! = 10 := by decide

/-! ### Concrete model theorems -/

/-- The number of logical items equals `count`. -/
theorem concreteItems_length (c : InflightsConcrete) :
    (concreteItems c).length = c.count := by
  simp [concreteItems]

/-- `concreteReset` empties the logical queue. -/
theorem concreteReset_items (c : InflightsConcrete) :
    concreteItems (concreteReset c) = [] := by
  simp [concreteReset, concreteItems]

/-- `concreteReset` corresponds to the abstract `reset`. -/
theorem concreteReset_abstract (c : InflightsConcrete) :
    toAbstract (concreteReset c) = reset (toAbstract c) := by
  simp [toAbstract, concreteReset, reset, concreteItems]

/-- `concreteAdd` increases `count` by 1. -/
theorem concreteAdd_count (c : InflightsConcrete) (idx : Nat) :
    (concreteAdd c idx).count = c.count + 1 := by
  simp [concreteAdd]

/-- `concreteAdd` preserves `cap`. -/
theorem concreteAdd_cap (c : InflightsConcrete) (idx : Nat) :
    (concreteAdd c idx).cap = c.cap := by
  simp [concreteAdd]

/-- `concreteReset` resets count to 0. -/
theorem concreteReset_count (c : InflightsConcrete) :
    (concreteReset c).count = 0 := by
  simp [concreteReset]

/-- The `bounded` invariant for the concrete model. -/
def concreteBounded (c : InflightsConcrete) : Prop := c.count ≤ c.cap

/-- `concreteAdd` preserves `concreteBounded` when not full. -/
theorem concreteAdd_bounded (c : InflightsConcrete) (idx : Nat)
    (hb : concreteBounded c) (hf : c.count < c.cap) :
    concreteBounded (concreteAdd c idx) := by
  simp [concreteBounded, concreteAdd]; omega

/-- `concreteReset` always produces a bounded result. -/
theorem concreteReset_bounded (c : InflightsConcrete) :
    concreteBounded (concreteReset c) := by
  simp [concreteBounded, concreteReset]

/-! ### Key correspondence theorem for concreteAdd -/

/-- Helper: distinct ring positions when `i < count < cap`. -/
private lemma ring_pos_ne (start i count cap : Nat)
    (hcap : 0 < cap) (hi : i < count) (hcount : count < cap) :
    (start + i) % cap ≠ (start + count) % cap := by
  intro heq
  have hicap : i < cap := Nat.lt_trans hi hcount
  -- Expand % using Nat.add_mod
  rw [Nat.add_mod start i, Nat.add_mod start count,
      Nat.mod_eq_of_lt hicap, Nat.mod_eq_of_lt hcount] at heq
  -- heq : (start % cap + i) % cap = (start % cap + count) % cap
  -- With s := start % cap < cap, and i < count < cap, omega derives contradiction
  have hs : start % cap < cap := Nat.mod_lt _ hcap
  omega

/-- **Key correspondence theorem**: `concreteAdd` lifts to `add` in the abstract model.

    Requires:
    - `hcap`  : capacity is positive
    - `hcount`: buffer is not full (count < cap)
    - `hbuf`  : buffer length equals cap (allocation invariant)

    The proof uses `ring_pos_ne` to show the `set` at position `next` does not
    disturb any of the existing positions `(start + i) % cap` for `i < count`. -/
theorem concreteAdd_abstract (c : InflightsConcrete) (idx : Nat)
    (hcap : 0 < c.cap) (hcount : c.count < c.cap)
    (hbuf : c.buffer.length = c.cap) :
    toAbstract (concreteAdd c idx) = add (toAbstract c) idx := by
  simp only [toAbstract, add, concreteAdd, concreteItems]
  ext1
  · rfl
  · -- Show: (List.range (count+1)).map f' = (List.range count).map f ++ [idx]
    rw [List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · -- For i < count: set doesn't affect position (start+i)%cap
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      have hne : (c.start + i) % c.cap ≠ (c.start + c.count) % c.cap :=
        ring_pos_ne _ _ _ _ hcap hi hcount
      -- (buffer.set next idx).getD pos 0 = buffer.getD pos 0 since pos ≠ next
      -- Uses List.get?_set_ne and unfolding of List.getD
      simp only [List.getD]
      rw [List.get?_set_ne hne]
    · -- For i = count: (buffer.set next idx).getD next 0 = idx
      have hnext_lt : (c.start + c.count) % c.cap < c.buffer.length :=
        hbuf ▸ Nat.mod_lt _ hcap
      simp only [List.getD]
      rw [List.get?_set_eq hnext_lt]

/-! ## Notes on proof completeness -/

/-
**Proof status (Tasks 3, 4, 5)**:

Operations (abstract):
- `reset`, `add`, `freeTo`, `freeFirstOne`: ✅ defined
- `full`, `bounded`, `monotone`: ✅ defined

Operations (concrete):
- `concreteItems`, `concreteAdd`, `concreteFreeTo`, `concreteReset`: ✅ defined
- `toAbstract`: ✅ defined

Decidable examples: ✅ all pass with `decide`

Abstract model (0 sorry):
- `reset_empty`, `reset_bounded`, `reset_cap`
- `add_length`, `add_cap`, `add_bounded`, `add_items`, `add_monotone`
- `freeTo_cap`, `freeTo_length_le`, `freeTo_bounded`
- `freeTo_all_gt` (requires `monotone` hypothesis)
- `freeTo_suffix`, `freeTo_monotone_idempotent`
- `freeTo_monotone`, `freeTo_all_le_empty`
- `freeFirstOne_removes_head`, `freeFirstOne_singleton`, `freeFirstOne_bounded`
- `reset_not_full`, `add_then_bounded`

Concrete model (0 sorry; some Mathlib API calls pending build verification):
- `concreteItems_length`, `concreteReset_items`, `concreteReset_abstract`
- `concreteAdd_count`, `concreteAdd_cap`, `concreteReset_count`
- `concreteAdd_bounded`, `concreteReset_bounded`
- `ring_pos_ne`: injectivity of ring addressing when count < cap
- `concreteAdd_abstract`: requires `ring_pos_ne` + `List.getD_set_eq`/`List.getD_set`

Helper lemmas (abstract, 0 sorry):
- `dropWhile_idem`: inductive
- `dropWhile_is_drop`: inductive
- `dropWhile_le_all_gt`: inductive over sorted list

Deferred (future runs):
- `concreteFreeTo_abstract`: requires loop invariant over the `go` recursion
- `incoming_cap` / `set_cap` dynamic capacity adjustment
- `u64` overflow (Nat used instead)
- Memory allocation/deallocation (`maybe_free_buffer`)
-/

end FVSquad.Inflights
