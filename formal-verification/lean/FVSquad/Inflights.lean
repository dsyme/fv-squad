/-!
# Inflights — Lean 4 Specification and Implementation Model

> 🔬 *Lean Squad — automated formal verification for `dsyme/fv-squad`.*

Formal specification and implementation model of the `Inflights` ring buffer from
`src/tracker/inflights.rs`.

## Purpose

`Inflights` is a bounded FIFO buffer tracking in-flight Raft message indices sent
to a single peer. It enforces that at most `cap` messages are in-flight at once.

## Abstract model

We model `Inflights` abstractly as:

```
{ queue : List Nat, cap : Nat }
```

* `queue`: the ordered sequence of in-flight indices, oldest at the front.
* `cap`: maximum simultaneous in-flight count.

The concrete ring-buffer representation (`start`, `buffer`, `count`, `incoming_cap`)
is fully abstracted away. In particular, `set_cap` / `incoming_cap` are omitted
from this model.

## Approximations and omissions

* **Ring-buffer layout**: `start`, `count`, `buffer` are abstracted as a plain `List`.
* **`incoming_cap` / `set_cap`**: dynamic capacity changes not modelled.
* **`u64` overflow**: indices modelled as `Nat` (unbounded), so no overflow.
* **Panics**: `add` on full buffer panics in Rust; the precondition `count < cap`
  rules this out in the Lean model.
* **`maybe_free_buffer`**: pure memory management, no semantic effect; omitted.
* **Sortedness**: the queue is **not** enforced as sorted by the type; theorems that
  require sortedness (P7, P9) take it as a `List.Pairwise (· ≤ ·)` hypothesis.

## Task coverage

* **Task 3** (Formal Spec Writing): Types, function model, and correctness
  theorems INF1–INF15 covering count/cap invariant, add semantics, free_to
  semantics, free_first_one equivalence, reset, and sortedness preservation.
-/

namespace FVSquad.Inflights

/-! ## State model -/

/-- Abstract model of an `Inflights` buffer.

    `queue` is the ordered sequence of in-flight message indices (oldest first).
    `cap` is the maximum permitted queue length. -/
structure Inflights where
  queue : List Nat
  cap   : Nat

/-! ## Operations -/

/-- The number of in-flight messages. -/
def Inflights.count (inf : Inflights) : Nat := inf.queue.length

/-- True iff the buffer is at capacity. -/
def Inflights.full (inf : Inflights) : Bool := inf.queue.length == inf.cap

/-- Append a new in-flight index to the back.
    Precondition: `count < cap` (panics in Rust if violated). -/
def Inflights.add (inf : Inflights) (x : Nat) : Inflights :=
  { inf with queue := inf.queue ++ [x] }

/-- Drop the longest leading prefix whose elements are ≤ `to`.

    This is the pure functional model of `free_to`:
    it acknowledges all entries with index ≤ `to`, removing them from the front
    of the queue, stopping at the first entry with index > `to`. -/
def dropLeq (to : Nat) : List Nat → List Nat
  | []      => []
  | h :: t  => if h ≤ to then dropLeq to t else h :: t

/-- Free all in-flight messages with index ≤ `to`.

    Corresponds to `Inflights::free_to`. -/
def Inflights.freeTo (inf : Inflights) (to : Nat) : Inflights :=
  { inf with queue := dropLeq to inf.queue }

/-- Free the first (oldest) in-flight message.

    Corresponds to `Inflights::free_first_one`. -/
def Inflights.freeFirstOne (inf : Inflights) : Inflights :=
  match inf.queue with
  | []      => inf
  | x :: _  => inf.freeTo x

/-- Clear all in-flight messages.

    Corresponds to `Inflights::reset`. -/
def Inflights.reset (inf : Inflights) : Inflights :=
  { inf with queue := [] }

/-! ## Examples (from Rust test suite) -/

#eval (show List Nat from
  let inf := Inflights.mk [] 10
  let inf := List.foldl (fun s x => s.add x) inf (List.range 10)
  (inf.freeTo 4).queue)  -- expected: [5, 6, 7, 8, 9]

#eval (show List Nat from
  let inf := Inflights.mk [] 10
  let inf := List.foldl (fun s x => s.add x) inf (List.range 10)
  (inf.freeFirstOne).queue)  -- expected: [1, 2, 3, 4, 5, 6, 7, 8, 9]

/-! ## INF1–INF4: Add semantics -/

/-- INF1: `add` appends to the back of the queue. -/
theorem inflights_add_queue (inf : Inflights) (x : Nat) :
    (inf.add x).queue = inf.queue ++ [x] := rfl

/-- INF2: `add` increments count by 1. -/
theorem inflights_add_count (inf : Inflights) (x : Nat) :
    (inf.add x).count = inf.count + 1 := by
  simp [Inflights.count, Inflights.add, List.length_append]

/-- INF3: `add` makes `x` a member of the queue. -/
theorem inflights_add_mem (inf : Inflights) (x : Nat) :
    x ∈ (inf.add x).queue := by
  simp [Inflights.add]

/-- INF4: `add` does not exceed cap (when precondition `count < cap` holds). -/
theorem inflights_count_le_cap (inf : Inflights) (x : Nat)
    (h : inf.count < inf.cap) :
    (inf.add x).count ≤ inf.cap := by
  simp only [Inflights.count] at *
  simp [Inflights.add, List.length_append]
  omega

/-! ## INF5: Full iff count = cap -/

/-- INF5: `full` is true iff count equals cap. -/
theorem inflights_full_iff (inf : Inflights) :
    inf.full = true ↔ inf.count = inf.cap := by
  simp [Inflights.full, Inflights.count, beq_iff_eq]

/-! ## INF6–INF10: freeTo semantics -/

/-- Helper: `dropLeq to q` is the queue after freeing entries ≤ `to`. -/
theorem inflights_freeTo_queue (inf : Inflights) (to : Nat) :
    (inf.freeTo to).queue = dropLeq to inf.queue := rfl

/-- INF6: `freeTo` does not increase count. -/
theorem inflights_freeTo_count_le (inf : Inflights) (to : Nat) :
    (inf.freeTo to).count ≤ inf.count := by
  simp only [Inflights.count, Inflights.freeTo]
  suffices ∀ q : List Nat, (dropLeq to q).length ≤ q.length from this inf.queue
  intro q
  induction q with
  | nil  => simp [dropLeq]
  | cons a t ih =>
    simp only [dropLeq]
    by_cases ha : a ≤ to
    · rw [if_pos ha]
      simp only [List.length_cons]
      omega
    · rw [if_neg ha]
      simp [List.length_cons]

/-- Key lemma: the first element of a non-empty `dropLeq` result is > `to`. -/
theorem dropLeq_head_gt (to : Nat) (q : List Nat) (x : Nat)
    (h : (dropLeq to q).head? = some x) : to < x := by
  induction q with
  | nil  => simp [dropLeq] at h
  | cons a t ih =>
    simp only [dropLeq] at h
    by_cases ha : a ≤ to
    · rw [if_pos ha] at h; exact ih h
    · rw [if_neg ha] at h
      simp [List.head?] at h
      omega

/-- INF7: If the result of `freeTo` is non-empty, its head is > `to`. -/
theorem inflights_freeTo_head_gt (inf : Inflights) (to x : Nat)
    (h : (inf.freeTo to).queue.head? = some x) : to < x :=
  dropLeq_head_gt to inf.queue x h

/-- INF8: Under sortedness, every element in the `freeTo` result is > `to`.

    This requires the queue to be sorted non-decreasingly, which holds in practice
    since Raft always adds entries in non-decreasing index order. -/
theorem inflights_freeTo_all_gt_sorted (inf : Inflights) (to : Nat)
    (hsort : inf.queue.Pairwise (· ≤ ·))
    (x : Nat) (hx : x ∈ (inf.freeTo to).queue) : to < x := by
  simp only [Inflights.freeTo] at hx
  suffices ∀ q : List Nat, q.Pairwise (· ≤ ·) → x ∈ dropLeq to q → to < x from
    this inf.queue hsort hx
  intro q hs hm
  induction q with
  | nil  => simp [dropLeq] at hm
  | cons a t ih =>
    simp only [dropLeq] at hm
    by_cases ha : a ≤ to
    · rw [if_pos ha] at hm
      exact ih (List.pairwise_cons.mp hs).2 hm
    · rw [if_neg ha] at hm
      cases hm with
      | head => omega
      | tail _ hxt =>
        have hat : ∀ b ∈ t, a ≤ b := (List.pairwise_cons.mp hs).1
        have hax : a ≤ x := hat x hxt
        omega

/-- INF9: `freeTo` preserves sortedness. -/
theorem inflights_freeTo_sorted (inf : Inflights) (to : Nat)
    (hsort : inf.queue.Pairwise (· ≤ ·)) :
    (inf.freeTo to).queue.Pairwise (· ≤ ·) := by
  simp only [Inflights.freeTo]
  suffices ∀ q : List Nat, q.Pairwise (· ≤ ·) → (dropLeq to q).Pairwise (· ≤ ·) from
    this inf.queue hsort
  intro q hs
  induction q with
  | nil  => simp [dropLeq, List.Pairwise.nil]
  | cons a t ih =>
    simp only [dropLeq]
    by_cases ha : a ≤ to
    · rw [if_pos ha]
      exact ih (List.pairwise_cons.mp hs).2
    · rw [if_neg ha]
      exact hs

/-- INF10: If the first element is > `to`, `freeTo` is a no-op. -/
theorem inflights_freeTo_noop (inf : Inflights) (to a : Nat) (t : List Nat)
    (hq : inf.queue = a :: t)
    (ha : to < a) :
    (inf.freeTo to).queue = inf.queue := by
  simp only [Inflights.freeTo, hq, dropLeq, if_neg (Nat.not_le.mpr ha)]

/-! ## INF11–INF12: freeFirstOne semantics -/

/-- INF11: On a non-empty queue, `freeFirstOne` equals `freeTo(head)`. -/
theorem inflights_freeFirstOne_eq_freeTo (inf : Inflights) (h : Nat) (t : List Nat)
    (hq : inf.queue = h :: t) :
    inf.freeFirstOne = inf.freeTo h := by
  simp [Inflights.freeFirstOne, hq]

/-- INF12: On an empty queue, `freeFirstOne` is the identity. -/
theorem inflights_freeFirstOne_empty (inf : Inflights)
    (hq : inf.queue = []) :
    inf.freeFirstOne = inf := by
  simp [Inflights.freeFirstOne, hq]

/-! ## INF13–INF15: reset semantics -/

/-- INF13: `reset` clears the queue. -/
theorem inflights_reset_queue (inf : Inflights) :
    (inf.reset).queue = [] := rfl

/-- INF14: `reset` sets count to 0. -/
theorem inflights_reset_count (inf : Inflights) :
    (inf.reset).count = 0 := by
  simp [Inflights.count, Inflights.reset]

/-- INF15: `reset` preserves capacity. -/
theorem inflights_reset_cap (inf : Inflights) :
    (inf.reset).cap = inf.cap := rfl

/-!
## Task 5: Additional Abstract Model Properties

These theorems extend the abstract model with properties useful for reasoning
about sequences of operations.
-/

/-- Helper: `dropLeq to` applied twice is the same as once. -/
theorem dropLeq_idempotent (to : Nat) (q : List Nat) :
    dropLeq to (dropLeq to q) = dropLeq to q := by
  induction q with
  | nil => simp [dropLeq]
  | cons a t ih =>
    simp only [dropLeq]
    by_cases ha : a ≤ to
    · rw [if_pos ha]; exact ih
    · rw [if_neg ha]; simp only [dropLeq, if_neg ha]

/-- INF16: `freeTo` is idempotent — freeing twice is the same as freeing once. -/
theorem inflights_freeTo_idem (inf : Inflights) (to : Nat) :
    (inf.freeTo to).freeTo to = inf.freeTo to := by
  simp only [Inflights.freeTo, dropLeq_idempotent]

/-- Helper: `dropLeq` result is a suffix of the original list. -/
theorem dropLeq_is_suffix (to : Nat) (q : List Nat) :
    (dropLeq to q) <:+ q := by
  induction q with
  | nil => simp [dropLeq]
  | cons a t ih =>
    simp only [dropLeq]
    by_cases ha : a ≤ to
    · rw [if_pos ha]
      exact ih.trans (List.suffix_cons a t)
    · rw [if_neg ha]
      exact List.suffix_refl (a :: t)

/-- INF17: `freeTo` result is a suffix of the original queue. -/
theorem inflights_freeTo_suffix (inf : Inflights) (to : Nat) :
    (inf.freeTo to).queue <:+ inf.queue :=
  dropLeq_is_suffix to inf.queue

/-- Helper: all elements dropped by `dropLeq` are ≤ `to`. -/
theorem dropLeq_dropped_le (to : Nat) (q : List Nat)
    (hsort : q.Pairwise (· ≤ ·)) :
    ∀ x ∈ q, x ∉ (dropLeq to q) → x ≤ to := by
  induction q with
  | nil => simp [dropLeq]
  | cons a t ih =>
    intro x hx hn
    simp only [dropLeq] at hn
    by_cases ha : a ≤ to
    · rw [if_pos ha] at hn
      cases hx with
      | head => exact ha
      | tail _ hxt => exact ih (List.pairwise_cons.mp hsort).2 x hxt hn
    · rw [if_neg ha] at hn
      exact absurd hx (by simp [hn])

/-- INF18: Under sortedness, `freeTo` removes exactly the prefix ≤ `to`.

    Specifically, no element > `to` is removed. -/
theorem inflights_freeTo_preserves_gt (inf : Inflights) (to : Nat)
    (hsort : inf.queue.Pairwise (· ≤ ·))
    (x : Nat) (hx : x ∈ inf.queue) (hgt : x > to) :
    x ∈ (inf.freeTo to).queue := by
  simp only [Inflights.freeTo]
  suffices ∀ q : List Nat, q.Pairwise (· ≤ ·) → x ∈ q → x > to → x ∈ dropLeq to q from
    this inf.queue hsort hx hgt
  intro q hs hm hgt'
  induction q with
  | nil => simp at hm
  | cons a t ih =>
    simp only [dropLeq]
    by_cases ha : a ≤ to
    · rw [if_pos ha]
      cases hm with
      | head => omega
      | tail _ hxt => exact ih (List.pairwise_cons.mp hs).2 hxt
    · rw [if_neg ha]
      exact hm

/-!
## Task 4: Concrete Ring-Buffer Implementation Model

The abstract `Inflights` model uses a plain `List Nat` for the queue. The Rust
implementation (`src/tracker/inflights.rs`) uses a ring buffer:

```rust
pub struct Inflights {
    start: usize,   // index of oldest entry in buffer
    count: usize,   // number of active entries
    buffer: Vec<u64>,  // ring buffer (capacity = cap)
    cap: usize,        // maximum inflight count
}
```

This section defines a pure functional model of the ring buffer and proves that
its operations correspond to the abstract `Inflights` model via the abstraction
function `InflightsConc.toAbstract`.

### Model approximations (same as abstract model)

- `u64` indices modelled as `Nat` (no overflow)
- `add` panic (full buffer) omitted — precondition `count < cap` rules it out
- `incoming_cap` / `set_cap` not modelled (dynamic capacity changes)
- `maybe_free_buffer` has no semantic effect; omitted
- `buffer` here is a `List Nat` (fixed length `cap`), not a `Vec<u64>`
-/

/-- Get element `i` from list, returning `0` for out-of-bounds. -/
private def listGet : List Nat → Nat → Nat
  | [], _ => 0
  | h :: _, 0 => h
  | _ :: t, n + 1 => listGet t n

/-- Set element at position `i` in list (uses stdlib List.set). -/
private abbrev listSet := @List.set Nat

/-- Extract `count` elements from a ring buffer starting at `start`, wrapping at `cap`.

    When `cap = 0` or `count = 0`, returns `[]`.
    Models the logical content of the ring buffer: positions
    `start, (start+1)%cap, ..., (start+count-1)%cap`. -/
def extractRing (buf : List Nat) (cap : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, start =>
    if 0 < cap then
      listGet buf (start % cap) :: extractRing buf cap n ((start + 1) % cap)
    else []

/-- Concrete ring-buffer model of `Inflights` (mirrors `src/tracker/inflights.rs`).

    Invariant (maintained by operations, not enforced in the type):
    - `count ≤ cap`
    - `cap = 0 ∨ start < cap`
    - `buffer.length = cap`                                                    -/
structure InflightsConc where
  buffer : List Nat  -- ring buffer slots (length = cap)
  start  : Nat       -- index of oldest in-flight entry (< cap)
  count  : Nat       -- number of active entries (≤ cap)
  cap    : Nat       -- declared capacity

/-- Well-formedness invariant for `InflightsConc`. -/
def InflightsConc.Inv (s : InflightsConc) : Prop :=
  s.count ≤ s.cap ∧
  (s.cap = 0 ∨ s.start < s.cap) ∧
  s.buffer.length = s.cap

/-- The logical queue extracted from the concrete ring buffer. -/
def InflightsConc.logicalContent (s : InflightsConc) : List Nat :=
  extractRing s.buffer s.cap s.count s.start

/-- Abstraction map: concrete state → abstract `Inflights`. -/
def InflightsConc.toAbstract (s : InflightsConc) : Inflights :=
  { queue := s.logicalContent, cap := s.cap }

/-- Create a new empty `InflightsConc`. Corresponds to `Inflights::new`. -/
def InflightsConc.new (cap : Nat) : InflightsConc :=
  { buffer := List.replicate cap 0, start := 0, count := 0, cap := cap }

/-- Add an entry to the ring buffer. Corresponds to `Inflights::add`.
    Precondition: `count < cap`. -/
def InflightsConc.addConc (s : InflightsConc) (x : Nat) : InflightsConc :=
  let cap' := if s.cap = 0 then 1 else s.cap
  let next := (s.start + s.count) % cap'
  { s with buffer := listSet s.buffer next x, count := s.count + 1 }

/-- Count how many leading entries are ≤ `to`, starting at `start`. -/
private def freeCount (buf : List Nat) (cap : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, start, to =>
    if 0 < cap then
      if listGet buf (start % cap) ≤ to then
        1 + freeCount buf cap n ((start + 1) % cap) to
      else 0
    else 0

/-- Free all entries with index ≤ `to`. Corresponds to `Inflights::free_to`. -/
def InflightsConc.freeToConc (s : InflightsConc) (to : Nat) : InflightsConc :=
  if 0 < s.cap then
    let freed := freeCount s.buffer s.cap s.count s.start to
    { s with start := (s.start + freed) % s.cap, count := s.count - freed }
  else s

/-- Free the oldest in-flight entry. Corresponds to `Inflights::free_first_one`. -/
def InflightsConc.freeFirstOneConc (s : InflightsConc) : InflightsConc :=
  if 0 < s.cap ∧ 0 < s.count then
    let head := listGet s.buffer (s.start % s.cap)
    s.freeToConc head
  else s

/-- Reset: clear all entries. Corresponds to `Inflights::reset`. -/
def InflightsConc.resetConc (s : InflightsConc) : InflightsConc :=
  { s with start := 0, count := 0 }

/-! ### Provable structural properties -/

/-- INF19: `new cap` satisfies the well-formedness invariant. -/
theorem inflightsConc_new_inv (cap : Nat) : (InflightsConc.new cap).Inv := by
  refine ⟨Nat.zero_le cap, ?_, ?_⟩
  · by_cases h : cap = 0
    · left; exact h
    · right; exact Nat.pos_of_ne_zero h
  · simp [InflightsConc.new, List.length_replicate]

/-- INF20: `new cap` has zero count. -/
theorem inflightsConc_new_count (cap : Nat) :
    (InflightsConc.new cap).count = 0 := rfl

/-- INF21: `new cap` has the given capacity. -/
theorem inflightsConc_new_cap (cap : Nat) :
    (InflightsConc.new cap).cap = cap := rfl

/-- INF22: `new cap` has empty logical content. -/
theorem inflightsConc_new_content (cap : Nat) :
    (InflightsConc.new cap).logicalContent = [] := by
  simp [InflightsConc.logicalContent, InflightsConc.new, extractRing]

/-- INF23: `addConc` increments count by 1. -/
theorem inflightsConc_add_count (s : InflightsConc) (x : Nat) :
    (s.addConc x).count = s.count + 1 := rfl

/-- INF24: `addConc` preserves capacity. -/
theorem inflightsConc_add_cap (s : InflightsConc) (x : Nat) :
    (s.addConc x).cap = s.cap := rfl

/-- INF25: `resetConc` sets count to 0. -/
theorem inflightsConc_reset_count (s : InflightsConc) :
    (s.resetConc).count = 0 := rfl

/-- INF26: `resetConc` preserves capacity. -/
theorem inflightsConc_reset_cap (s : InflightsConc) :
    (s.resetConc).cap = s.cap := rfl

/-- INF27: `resetConc` clears the logical content. -/
theorem inflightsConc_reset_content (s : InflightsConc) :
    (s.resetConc).logicalContent = [] := by
  simp [InflightsConc.logicalContent, InflightsConc.resetConc, extractRing]

/-- Helper: length of `extractRing` equals `count` when `cap > 0`. -/
theorem extractRing_length (buf : List Nat) (cap : Nat) (h_cap : 0 < cap) :
    ∀ (count start : Nat), (extractRing buf cap count start).length = count := by
  intro count
  induction count with
  | zero => intro; simp [extractRing]
  | succ n ih =>
    intro start
    simp [extractRing, if_pos h_cap, ih]

/-- INF28: The logical content length equals `count` (when `cap > 0`). -/
theorem inflightsConc_content_length (s : InflightsConc)
    (h_cap : 0 < s.cap) :
    s.logicalContent.length = s.count :=
  extractRing_length s.buffer s.cap h_cap s.count s.start

/-- Helper: `listGet` returns 0 for out-of-bounds. -/
theorem listGet_out_of_bounds (l : List Nat) (i : Nat) (h : l.length ≤ i) :
    listGet l i = 0 := by
  induction l generalizing i with
  | nil => simp [listGet]
  | cons a t ih =>
    cases i with
    | zero => simp at h
    | succ n => exact ih n (Nat.le_of_succ_le_succ h)

/-- Helper: `listSet` (= List.set) preserves length. -/
theorem listSet_length (l : List Nat) (i : Nat) (v : Nat) :
    (listSet l i v).length = l.length :=
  List.length_set

/-- INF29: `addConc` preserves the buffer length (invariant: buffer.length = cap). -/
theorem inflightsConc_add_buf_length (s : InflightsConc)
    (h_inv : s.Inv) (x : Nat) :
    (s.addConc x).buffer.length = s.cap := by
  simp only [InflightsConc.addConc]
  exact (listSet_length s.buffer _ _).trans h_inv.2.2

/-! ### Helper lemmas for ring-buffer correspondence proofs -/

/-- `listGet` at the index just set returns the new value. -/
private theorem listGet_set_eq (l : List Nat) (i v : Nat) (hi : i < l.length) :
    listGet (l.set i v) i = v := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons a t ih =>
    cases i with
    | zero => simp [List.set, listGet]
    | succ n => exact ih n (Nat.lt_of_succ_lt_succ hi)

/-- `listGet` at a different index is unchanged by `set`. -/
private theorem listGet_set_ne (l : List Nat) (i j v : Nat) (hij : i ≠ j) :
    listGet (l.set i v) j = listGet l j := by
  induction l generalizing i j with
  | nil => simp [List.set, listGet]
  | cons a t ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ m => simp [List.set, listGet]
    | succ n =>
      cases j with
      | zero => simp [List.set, listGet]
      | succ m =>
        simp only [List.set, listGet]
        exact ih n m (fun h => hij (congrArg Nat.succ h))

/-- Helper: one unfolding step of `extractRing` when `cap > 0`. -/
private theorem extractRing_succ (buf : List Nat) (cap : Nat) (h_cap : 0 < cap) (n start : Nat) :
    extractRing buf cap (n + 1) start =
    listGet buf (start % cap) :: extractRing buf cap n ((start + 1) % cap) := by
  simp [extractRing, h_cap]

/-- `extractRing` is insensitive to reducing `start` modulo `cap`. -/
private theorem extractRing_mod_start (buf : List Nat) (cap : Nat) (h_cap : 0 < cap) :
    ∀ (count start : Nat),
    extractRing buf cap count (start % cap) = extractRing buf cap count start := by
  intro count
  induction count with
  | zero => intro; simp [extractRing]
  | succ n ih =>
    intro start
    rw [extractRing_succ _ _ h_cap, extractRing_succ _ _ h_cap,
        Nat.mod_eq_of_lt (Nat.mod_lt start h_cap), Nat.mod_add_mod]

/-- The last element appended by `extractRing` sits at `(start + count) % cap`. -/
private theorem extractRing_append_last (buf : List Nat) (cap : Nat) (h_cap : 0 < cap) :
    ∀ (count start : Nat),
    extractRing buf cap (count + 1) start =
    extractRing buf cap count start ++ [listGet buf ((start + count) % cap)] := by
  intro count
  induction count with
  | zero => intro start; simp [extractRing, h_cap]
  | succ n ih =>
    intro start
    have lhs_step : extractRing buf cap (n + 1 + 1) start =
                    listGet buf (start % cap) :: extractRing buf cap (n + 1) ((start + 1) % cap) :=
      extractRing_succ buf cap h_cap (n + 1) start
    have rhs_step : extractRing buf cap (n + 1) start =
                    listGet buf (start % cap) :: extractRing buf cap n ((start + 1) % cap) :=
      extractRing_succ buf cap h_cap n start
    rw [lhs_step, ih ((start + 1) % cap), rhs_step, List.cons_append]
    congr 1
    rw [Nat.mod_add_mod (start + 1) cap n, show start + 1 + n = start + (n + 1) from by omega]

/-- In a ring buffer with `count < cap`, positions `(start+i)%cap` for `i ≤ count` are
    distinct — specifically, `(start+i)%cap ≠ (start+count)%cap` for `i < count`. -/
private theorem ring_positions_ne (cap start count i : Nat) (h_cap : 0 < cap)
    (h_count : count < cap) (hi : i < count) :
    (start + i) % cap ≠ (start + count) % cap := by
  intro heq
  have hci_pos : 0 < count - i := Nat.sub_pos_of_lt hi
  have hci_lt : count - i < cap := Nat.lt_of_le_of_lt (Nat.sub_le count i) h_count
  have h1 := Nat.add_mod (start + i) (count - i) cap
  rw [show start + i + (count - i) = start + count from by omega] at h1
  have key : (start + i) % cap = ((start + i) % cap + (count - i) % cap) % cap := heq.trans h1
  have hr_lt : (start + i) % cap < cap := Nat.mod_lt _ h_cap
  have hd_lt : (count - i) % cap < cap := Nat.mod_lt _ h_cap
  have hd_pos : 0 < (count - i) % cap := by rw [Nat.mod_eq_of_lt hci_lt]; exact hci_pos
  have hmod : ((start + i) % cap + (count - i) % cap) % cap = (start + i) % cap := key.symm
  by_cases hlt : (start + i) % cap + (count - i) % cap < cap
  · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
  · have hge : cap ≤ (start + i) % cap + (count - i) % cap := Nat.le_of_not_lt hlt
    have heq2 : ((start + i) % cap + (count - i) % cap) % cap =
                (start + i) % cap + (count - i) % cap - cap := by
      have hlt2 : (start + i) % cap + (count - i) % cap - cap < cap := by omega
      calc ((start + i) % cap + (count - i) % cap) % cap
          = ((start + i) % cap + (count - i) % cap - cap + cap) % cap := by congr 1; omega
          _ = ((start + i) % cap + (count - i) % cap - cap) % cap := Nat.add_mod_right _ _
          _ = (start + i) % cap + (count - i) % cap - cap := Nat.mod_eq_of_lt hlt2
    rw [heq2] at hmod; omega

/-- Modifying a buffer position not accessed by `extractRing` leaves the result unchanged. -/
private theorem extractRing_set_indep (buf : List Nat) (cap : Nat) (h_cap : 0 < cap)
    (j v : Nat) :
    ∀ (count start : Nat),
    (∀ i, i < count → (start + i) % cap ≠ j) →
    extractRing (buf.set j v) cap count start = extractRing buf cap count start := by
  intro count
  induction count with
  | zero => intros; simp [extractRing]
  | succ n ih =>
    intro start hnotin
    rw [extractRing_succ _ _ h_cap, extractRing_succ _ _ h_cap]
    have h0 : start % cap ≠ j := by
      have := hnotin 0 (Nat.zero_lt_succ n); simp only [Nat.add_zero] at this; exact this
    rw [listGet_set_ne buf j (start % cap) v (Ne.symm h0)]
    congr 1
    apply ih ((start + 1) % cap)
    intro i hi
    have h1 := hnotin (i + 1) (Nat.succ_lt_succ hi)
    rwa [show start + (i + 1) = (start + 1) + i from by omega, ← Nat.mod_add_mod] at h1

/-- `freeCount` never exceeds the count argument. -/
private theorem freeCount_le (buf : List Nat) (cap : Nat) (to : Nat) :
    ∀ (count start : Nat), freeCount buf cap count start to ≤ count := by
  intro count
  induction count with
  | zero => intro; simp [freeCount]
  | succ n ih =>
    intro start
    simp only [freeCount]
    by_cases h_cap : 0 < cap
    · simp only [if_pos h_cap]
      by_cases hle : listGet buf (start % cap) ≤ to
      · simp only [if_pos hle]; have := ih ((start + 1) % cap); omega
      · simp only [if_neg hle]; exact Nat.zero_le _
    · simp only [if_neg h_cap]; exact Nat.zero_le _

/-- The `dropLeq` of an `extractRing` equals the `extractRing` after advancing `start`
    by the number of elements freed. -/
private theorem extractRing_dropLeq_eq (buf : List Nat) (cap : Nat) (h_cap : 0 < cap)
    (to : Nat) :
    ∀ (count start : Nat),
    dropLeq to (extractRing buf cap count start) =
    extractRing buf cap (count - freeCount buf cap count start to)
      ((start + freeCount buf cap count start to) % cap) := by
  intro count
  induction count with
  | zero =>
    intro start
    simp only [extractRing, freeCount, Nat.sub_zero, Nat.add_zero]
    simp [dropLeq]
  | succ n ih =>
    intro start
    rw [extractRing_succ _ _ h_cap]
    simp only [freeCount, if_pos h_cap]
    by_cases hle : listGet buf (start % cap) ≤ to
    · simp only [if_pos hle]
      have hdrop : dropLeq to (listGet buf (start % cap) ::
                    extractRing buf cap n ((start + 1) % cap)) =
                  dropLeq to (extractRing buf cap n ((start + 1) % cap)) := by
        simp [dropLeq, hle]
      rw [hdrop, ih ((start + 1) % cap)]
      have hf := freeCount_le buf cap to n ((start + 1) % cap)
      have h_cnt : n - freeCount buf cap n ((start + 1) % cap) to =
                   n + 1 - (1 + freeCount buf cap n ((start + 1) % cap) to) := by omega
      have h_st : ((start + 1) % cap + freeCount buf cap n ((start + 1) % cap) to) % cap =
                  (start + (1 + freeCount buf cap n ((start + 1) % cap) to)) % cap := by
        rw [Nat.mod_add_mod (start + 1) cap (freeCount buf cap n ((start + 1) % cap) to),
            show start + 1 + freeCount buf cap n ((start + 1) % cap) to =
                 start + (1 + freeCount buf cap n ((start + 1) % cap) to) from by omega]
      rw [← h_cnt, h_st]
    · simp only [if_neg hle, Nat.sub_zero, Nat.add_zero]
      have hkeep : dropLeq to (listGet buf (start % cap) ::
                    extractRing buf cap n ((start + 1) % cap)) =
                  listGet buf (start % cap) :: extractRing buf cap n ((start + 1) % cap) := by
        simp [dropLeq, hle]
      rw [hkeep, ← extractRing_succ buf cap h_cap n start]
      exact (extractRing_mod_start buf cap h_cap (n + 1) start).symm

/-! ### Correspondence theorems -/

/-- INF30: `addConc` corresponds to abstract `add`.

    Under the invariant, adding to the concrete ring buffer produces the same
    logical content as appending to the abstract list. -/
theorem inflightsConc_add_correct (s : InflightsConc) (x : Nat)
    (h_inv : s.Inv) (h_nf : s.count < s.cap) :
    (s.addConc x).toAbstract = s.toAbstract.add x := by
  have h_cap_pos : 0 < s.cap := Nat.lt_of_le_of_lt (Nat.zero_le s.count) h_nf
  have h_cap_ne : s.cap ≠ 0 := by omega
  -- Unfold and reduce: cap' = cap (since cap ≠ 0), next = (start+count)%cap
  simp only [InflightsConc.toAbstract, Inflights.add, InflightsConc.addConc, if_neg h_cap_ne,
             InflightsConc.logicalContent]
  congr 1
  -- Goal: extractRing (listSet s.buffer ((s.start+s.count)%s.cap) x) s.cap (s.count+1) s.start
  --       = extractRing s.buffer s.cap s.count s.start ++ [x]
  let next := (s.start + s.count) % s.cap
  calc extractRing (listSet s.buffer next x) s.cap (s.count + 1) s.start
      = extractRing (listSet s.buffer next x) s.cap s.count s.start ++
        [listGet (listSet s.buffer next x) ((s.start + s.count) % s.cap)] :=
          extractRing_append_last _ s.cap h_cap_pos s.count s.start
    _ = extractRing s.buffer s.cap s.count s.start ++
        [listGet (listSet s.buffer next x) next] := by
          rw [extractRing_set_indep s.buffer s.cap h_cap_pos next x s.count s.start
                (fun i hi => ring_positions_ne s.cap s.start s.count i h_cap_pos h_nf hi)]
    _ = extractRing s.buffer s.cap s.count s.start ++ [x] := by
          rw [listGet_set_eq s.buffer next x (h_inv.2.2 ▸ Nat.mod_lt _ h_cap_pos)]

/-- INF31: `freeToConc` corresponds to abstract `freeTo`.

    Under the invariant, freeing entries ≤ `to` in the concrete model
    matches `dropLeq to` on the abstract list. -/
theorem inflightsConc_freeTo_correct (s : InflightsConc) (to : Nat)
    (h_inv : s.Inv) :
    (s.freeToConc to).toAbstract = s.toAbstract.freeTo to := by
  have hcap : (s.freeToConc to).cap = s.cap := by
    simp only [InflightsConc.freeToConc]
    by_cases h : 0 < s.cap
    · simp [if_pos h]
    · simp [if_neg h]
  simp only [InflightsConc.toAbstract, Inflights.freeTo, hcap]
  congr 1
  -- Goal: logicalContent (freeToConc s to) = dropLeq to (logicalContent s)
  simp only [InflightsConc.logicalContent, InflightsConc.freeToConc]
  by_cases h_cap : 0 < s.cap
  · simp only [if_pos h_cap]
    -- Apply the dropLeq correspondence lemma
    rw [← extractRing_dropLeq_eq s.buffer s.cap h_cap to s.count s.start]
  · -- When cap = 0, both sides are []
    have h_cap_eq : s.cap = 0 := by omega
    have hext : ∀ (n start : Nat), extractRing s.buffer 0 n start = [] := by
      intro n; induction n with
      | zero => intro; simp [extractRing]
      | succ m ih => intro st; simp only [extractRing, if_neg (by omega : ¬(0 < 0))]
    simp [h_cap_eq, hext, dropLeq]

/-- INF32: `resetConc` corresponds to abstract `reset`. -/
theorem inflightsConc_reset_correct (s : InflightsConc) :
    s.resetConc.toAbstract = s.toAbstract.reset := by
  simp [InflightsConc.toAbstract, InflightsConc.resetConc, Inflights.reset,
        InflightsConc.logicalContent, extractRing]

end FVSquad.Inflights
