/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false

/-!
# Homework File for Week 6

There are 5 exercises. Each correctly solved exercise is worth 20 points.

All tactics **except `grind`, `waterfall`** are welcome. However, if you use `grind, waterfall`
in an exercise, you can still get up to half the points.

We also reserve the right to subtract points for unreadable code.
Please use the code style used in the lecture. If you deviate from it,
please explain why and what the code does in the comments.
-/

@[simp] def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y
@[simp] def Nat.MaxOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≥ y

namespace HW6

/-!
  **Exercise 1**

  Fast exponentiation computes `a ^ n` by recursively computing `a ^ (n / 2)` and squaring
  the result. Prove that it is correct (a), and that it needs at most `2 * log₂ n`
  multiplications (b).
-/

def square (b : ℕ) : ℕ := b * b

def fastPow (a n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n = 1 then a
  else if n % 2 = 0 then square (fastPow a (n / 2))
  else square (fastPow a (n / 2)) * a

-- The number of multiplications performed by `fastPow a n`:
-- `square` costs one multiplication, and the odd case needs one more.
def fastPowMuls (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 0
  else if n % 2 = 0 then fastPowMuls (n / 2) + 1
  else fastPowMuls (n / 2) + 2

-- **(a)** Prove the following theorem.
theorem fastPow_eq_pow (a n : ℕ) : fastPow a n = a ^ n := by
  sorry

/-
  Hint: You might find the following two theorems useful.
-/
#check Nat.log_div_base
#check Nat.log_pos

-- **(b)** Prove the following theorem.
theorem fastPowMuls_le (n : ℕ) : fastPowMuls n ≤ 2 * Nat.log 2 n := by
  sorry


/-!
  **Exercise 2**

  "Would you tell me, please, which way I ought to go from here?"
  "That depends a good deal on where you want to get to," said the Cat.
  "I don't much care where—" said Alice.
  "Then it doesn't matter which way you go," said the Cat.
  "—so long as I get somewhere," Alice added as an explanation.
  "Oh, you're sure to do that," said the Cat, "if you only walk long enough."

  Binary search finds the first position at which a monotone predicate `p` becomes true:
  if `p hi` holds, then `binSearch p lo hi` returns the smallest `k ≥ lo` with `p k`.
  In every step, the search interval `[lo, hi]` is halved.
  (`[DecidablePred p]` says that `p k` can be decided for every `k`, so that
  `if p mid then ... else ...` makes sense.)
-/

-- `p` is monotone if, once it holds, it holds for all larger numbers.
def MonotonePred (p : ℕ → Prop) : Prop := ∀ i j, i ≤ j → p i → p j

def binSearch (p : ℕ → Prop) [DecidablePred p] (lo hi : ℕ) : ℕ :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if p mid then
      -- if `p mid` then `res ≤ mid`
      binSearch p lo mid
    else
      -- else `res > mid`
      binSearch p (mid + 1) hi
  else hi
termination_by hi - lo

-- **(a)** Prove the following theorem.
theorem binSearch_true (p : ℕ → Prop) [DecidablePred p] (lo hi : ℕ) (h : p hi) :
    p (binSearch p lo hi) := by
  sorry

-- **(b)** Prove the following theorem.
theorem binSearch_least (p : ℕ → Prop) [DecidablePred p] (hp : MonotonePred p)
    (lo hi k : ℕ) (hlo : lo ≤ k) (hk : k < binSearch p lo hi) : ¬p k := by
  sorry


/-!
  **Exercise 3**

  "Let me see: four times five is twelve, and four times six is thirteen, and four times seven
  is—oh dear! I shall never get to twenty at that rate!"

  We use binary search to compute the integer square root `⌊√n⌋`, which is the first `k`
  with `k * k ≤ n < (k + 1) * (k + 1)`. Prove that `isqrt n` is indeed the integer square root,
  i.e. prove that `isqrt n * isqrt n ≤ n < (isqrt n + 1) * (isqrt n + 1)`.

  You may use the theorems from Exercise 2 even if you have not proven them.
-/

def isqrt (n : ℕ) : ℕ := binSearch (fun k => n < (k + 1) * (k + 1)) 0 n

/-
  Hint: `nlinarith` proves some non-linear inequalities, and consider the theorems:
-/
#check Nat.mul_self_le_mul_self
#check Nat.sub_add_cancel

-- **(a)** Prove the following theorem.
theorem lt_isqrt_succ_mul_self (n : ℕ) : n < (isqrt n + 1) * (isqrt n + 1) := by
  sorry

-- **(b)** Prove the following theorem.
theorem isqrt_mul_self_le (n : ℕ) : isqrt n * isqrt n ≤ n := by
  sorry


/-!
  **Exercise 4**

  Quicksort picks the head `x` of the list as pivot, splits the remaining elements into those
  smaller than `x` (`lower x xs`) and those at least `x` (`upper x xs`), and sorts both
  parts recursively.
-/
inductive Sorted : List ℕ → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a : ℕ) (t : List ℕ) : a.MinOfList t → Sorted t → Sorted (a :: t)

-- This is Exercise 3(b) of HW5. You do **not** need to fill in the `sorry`:
-- you may use this lemma without proving it.
lemma sorted_append (x : ℕ) (l1 l2 : List ℕ) (h1 : Sorted l1) (h2 : Sorted l2)
    (h1' : x.MaxOfList l1) (h2' : x.MinOfList l2) : Sorted (l1 ++ x :: l2) := by
  sorry

-- The elements of `xs` that are smaller than the pivot `x`.
def lower (x : ℕ) (xs : List ℕ) : List ℕ := xs.filter (· < x)

-- The elements of `xs` that are at least the pivot `x`.
def upper (x : ℕ) (xs : List ℕ) : List ℕ := xs.filter (· ≥ x)

@[simp] lemma mem_lower (x y : ℕ) (xs : List ℕ) :
    y ∈ lower x xs ↔ y ∈ xs ∧ y < x := by
  simp [lower]

@[simp] lemma mem_upper (x y : ℕ) (xs : List ℕ) :
    y ∈ upper x xs ↔ y ∈ xs ∧ x ≤ y := by
  simp [upper]

lemma length_lower_add_length_upper (x : ℕ) (xs : List ℕ) :
    (lower x xs).length + (upper x xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    unfold lower upper at *
    simp only [List.filter_cons]
    split_ifs <;> simp_all <;> omega

def quickSort (l : List ℕ) : List ℕ :=
  match l with
  | [] => []
  | x :: xs => quickSort (lower x xs) ++ x :: quickSort (upper x xs)
termination_by l.length
decreasing_by
  all_goals
    simp only [lower, upper, List.length_cons]
    apply Nat.lt_succ_of_le
    apply List.length_filter_le

-- **(a)** Prove the following theorem.
theorem mem_quickSort (y : ℕ) (l : List ℕ) : y ∈ quickSort l ↔ y ∈ l := by
  sorry

-- **(b)** Prove the following theorem.
theorem quickSort_sorted (l : List ℕ) : Sorted (quickSort l) := by
  sorry

/-!
  **Exercise 5**

  "And when they were up, they were up,
  And when they were down, they were down,
  And when they were only half-way up,
  They were neither up nor down."

  A peak of `f` on the interval `[a, b]` is a position `r ∈ [a, b]` whose value is at least
  the values of its neighbours inside the interval. Every `f` has a peak (e.g. a maximum), but
  finding a maximum requires looking at every value. Peak finding needs only logarithmically
  many steps: it compares `f mid` with `f (mid + 1)` and continues on the side that goes uphill.

  You may use the theorems from (a) and (b) for (c).
-/
def IsPeak (f : ℕ → ℕ) (a b r : ℕ) : Prop :=
  a ≤ r ∧ r ≤ b ∧ (r = a ∨ f (r - 1) ≤ f r) ∧ (r = b ∨ f (r + 1) ≤ f r)

def peak (f : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if f mid < f (mid + 1) then
      peak f (mid + 1) hi
    else
      peak f lo mid
  else lo
termination_by hi - lo

-- **(a)** Prove the following theorem.
theorem peak_isPeak_of_invariant (f : ℕ → ℕ) (a b lo hi : ℕ)
    (hab : a ≤ lo) (hlh : lo ≤ hi) (hhb : hi ≤ b)
    (hlo : lo = a ∨ f (lo - 1) < f lo) (hhi : hi = b ∨ f (hi + 1) ≤ f hi) :
    IsPeak f a b (peak f lo hi) := by
  sorry

-- **(b)** Prove the following theorem.
theorem peak_isPeak (f : ℕ → ℕ) (a b : ℕ) (hab : a ≤ b) : IsPeak f a b (peak f a b) := by
  sorry

-- **(c)** Prove the following theorem.
theorem peak_eq_of_unimodal (f : ℕ → ℕ) (a b m : ℕ) (ham : a ≤ m) (hmb : m ≤ b)
    (hinc : ∀ i, a ≤ i → i < m → f i < f (i + 1))
    (hdec : ∀ i, m ≤ i → i < b → f (i + 1) < f i) :
    peak f a b = m := by
  sorry

end HW6
