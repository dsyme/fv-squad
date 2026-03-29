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

end FVSquad.Inflights
