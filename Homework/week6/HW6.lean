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
-- **MyNote:** the idea is (x * x) * (x * x) is faster than x * (x * (x * x))
-- under reusing the squared number.
-- fastPow with n ∈ ℕ
--       ⎧ 1,              if n = 0
--       | a,              if n = 1
--  aⁿ = ⎨ (aⁿ⁄²)²,         if n even
--       ⎩ (aⁿ⁄²)² · a,     if n odd
---------------------------------------
theorem fastPow_eq_pow (a n : ℕ) : fastPow a n = a ^ n := by
  fun_induction fastPow with
  -- case 1, 2 are trivial by definitions
  | case1 =>
    rw [Nat.pow_zero]
  | case2 h =>
    rw [Nat.pow_one]
  --------------------------------
  -- case 3: the even case
  -- to show `square (fastPow a (n / 2)) = a ^ n`
  | case3 n h h1 h2 ih =>
    unfold square
    rw [ih, ← pow_add]
    -- now show powers equal
    have h_helper : (n / 2) + (n / 2) = n := by
      omega
    rw [h_helper]
  --------------------------------
    -- case 4: the odd case
    -- `square (fastPow a (n / 2)) * a = a ^ n`
  | case4 n h h1 h2 ih =>
    unfold square
    rw [ih, ← pow_add]
    rw [← pow_succ]
    -- use the helper to recover n, using that n is odd so twice the halved plus
    -- one is again n
    have h_helper : n / 2 + n / 2 + 1 = n := by
      omega
    rw [h_helper]

/-
  Hint: You might find the following two theorems useful.
-/
#check Nat.log_div_base -- ∀ (b n : ℕ), Nat.log b (n / b) = Nat.log b n - 1
#check Nat.log_pos      -- ∀ {b n : ℕ}, 1 < b → b ≤ n → 0 < Nat.log b n

-- **(b)** Prove the following theorem.
theorem fastPowMuls_le (n : ℕ) : fastPowMuls n ≤ 2 * Nat.log 2 n := by
  fun_induction fastPowMuls with
  | case1 => omega
  | case2 h => omega
  | case3 n h h1 h2 ih =>
    grw [ih, Nat.log_div_base]
    -- we just do some log tricks
    -- 2 * log(n/2) + 1 ≤ 2 * log(n)
    -- 2 * (log(n) - log(2)) + 1 ≤ 2 * log(n)
    -- 2 * (log(n) - 1) + 1 ≤ 2 * log(n)
    ------------------------------------
    -- now use positivity
    have h_helper : 0 < Nat.log 2 n := by
      apply Nat.log_pos
      -- case 1: to show 1 < 2
      · trivial
      -- case 2: to show 2 ≤ n
      · omega
    omega
  | case4 n h h1 h2 ih =>
    -- we already used it above in case 3
    have h_helper : 0 < Nat.log 2 n := by
      apply Nat.log_pos
      · trivial
      · omega
    -- use ih : fastPowMuls (n / 2) ≤ 2 * Nat.log 2 (n / 2)
    calc fastPowMuls (n / 2) + 2
        ≤ 2 * Nat.log 2 (n / 2) + 2 := by grw [ih]
      _ ≤ 2 * (Nat.log 2 n - 1) + 2 := by rw [Nat.log_div_base]
      _ ≤ 2 * Nat.log 2 n := by omega

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
  fun_induction binSearch with
  | case1 => expose_names; exact ih1 h_2
  | case2 => expose_names; exact ih1 h
  | case3 => expose_names; exact h

-- **(b)** Prove the following theorem.
theorem binSearch_least (p : ℕ → Prop) [DecidablePred p] (hp : MonotonePred p)
  (lo hi k : ℕ) (hlo : lo ≤ k) (hk : k < binSearch p lo hi) : ¬p k := by
  -- **MyNote:** Denote the result of binary search as `res`, the theorem says
  --   `res : ℕ := binSearch p lo hi`,
  -- ⇔ `res` indicates the least index in [lo, hi], where `p` is true
  -- ⇔ For any smaller indices k ∈ [lo, res) must not make `p` true.
  ------------------------------------------------
  rw [MonotonePred] at hp
  fun_induction binSearch with
  ----------------------------------------------
  -- Case 1:
  -- binSearch goes left, (p mid is true ∧ hi := mid), enter [lo, mid]
  --                res := hi'
  --                /
  --   lo         mid         hi
  --   ├───────────┤          |
  | case1 =>
    expose_names
    exact ih1 hlo hk -- by inductive hypothesis directly
  ----------------------------------------------
  -- Case 2: binSearch goes right, (p mid is false ∧ lo := mid + 1), enter [mid+1, hi]
  --   lo         mid         hi
  --   |           |  ├───────┤
  --                 mid+1
  --                    \
  --                    res := lo'
  | case2 =>
    expose_names
    -- case 2.1: k ≤ mid
    -- case 2.2: or ih1 : mid + 1 ≤ k → k < binSearch p (mid + 1) hi → ¬p k
    -- by showing mid + 1 ≤ k
    -- hk states k ∈ [lo', res'], res' is the new result after one recursion on [mid+1, hi]
    by_cases hk : k ≤ mid
    · apply hp at hk
      rw [imp_iff_not_or] at hk
      obtain hk_l | hk_r := hk
      · exact hk_l
      · contradiction
    · expose_names
      -- simple rewrite to match the form of the ih1
      have hk_rev : mid + 1 ≤ k := by
        omega
      exact ih1 hk_rev hk_1
  ----------------------------------------------
  -- Case 3:
  -- binSearch terminates when ¬ lo < hi, i.e. hi ≤ lo
  -- it must be that hi is k
  | case3 =>
    expose_names
    have h_rev : hi = k := by
      omega
    simp_all


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
#check Nat.mul_self_le_mul_self -- (h : m ≤ n) : m * m ≤ n * n
#check Nat.sub_add_cancel       -- (h : m ≤ n) : n - m + m = n

-- **MyNote:** In the following we will introduce some helpers
-- ➊ Predicate itself for `isqrt`, when k > ⌊√n⌋.
-- here for the decidable as a deriving property, we add this @[reducible] (not covered in class),
-- but found here https://proofassistants.stackexchange.com/questions/2457/what-is-the-precise-meaning-of-reducible
@[reducible] def pred (n k : ℕ) : Prop := n < (k + 1) * (k + 1)

-- ➋ monotonicity
-- i ≤ j → pred n i → pred n j
theorem pred_is_monotone (n : ℕ) : MonotonePred (pred n) := by
  unfold MonotonePred
  intro i j h h_
  simp_all only [pred]
  nlinarith

-- **(a)** Prove the following theorem.
theorem lt_isqrt_succ_mul_self (n : ℕ) : n < (isqrt n + 1) * (isqrt n + 1) := by
  unfold isqrt
  apply binSearch_true (pred n)
  -- after unfolding we can close the goal n < (n + 1) * (n + 1) directly
  unfold pred
  nlinarith

-- **(b)** Prove the following theorem.
theorem isqrt_mul_self_le (n : ℕ) : isqrt n * isqrt n ≤ n := by
  -- case 1: isqrt n = 0, trivial case
  by_cases h : isqrt n = 0
  · simp [h]
  -- case 2: since isqrt n ≠ 0 is a natural number, it is the successor
  -- of some natural number k ∈ ℕ.
  · obtain ⟨k, h_⟩ := Nat.exists_eq_succ_of_ne_zero h
    rw [h_]
    have hk : k < isqrt n := by omega
    -- using theorem binSearch_least with named construction for clarity
    have h_helper : ¬ pred n k :=
      binSearch_least
        (p := pred n)
        (hp := pred_is_monotone n)
        (lo := 0) (hi := n) (k := k)
        (hlo := Nat.zero_le k)
        (hk := hk)
    -- we obtain (k + 1) * (k + 1) ≤ n and close directly
    simp only [pred, Nat.not_lt] at h_helper
    exact h_helper

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
  fun_induction quickSort with
  | case1 => trivial -- y ∈ [] ↔ y ∈ []
  | case2 =>
    expose_names
    -- y ∈ quickSort (lower x xs) ++ x :: quickSort (upper x xs) ↔ y ∈ x :: xs
    constructor
    -- goal 1: y ∈ x :: xs
    -- if `h: y ∈ quickSort (lower x xs) ++ x :: quickSort (upper x xs)`
    · intro h
       -- explicitly write out `++` and lower, upper etc.
      simp_all only [List.mem_append, mem_lower, mem_upper, List.mem_cons]
      cases h <;> expose_names
      · right
        exact h.left
      · cases h <;> expose_names
        · left; exact h
        · right; exact h.left
    -------------------------------------------
    -- goal 2: y ∈ quickSort (lower x xs) ++ x :: quickSort (upper x xs)
    -- if y ∈ x :: xs
    · intro h
      simp_all only [List.mem_append, mem_lower, mem_upper, List.mem_cons]
      cases h <;> expose_names
      · right; left; exact h
      · simp_all only [true_and] -- simp_all?
        omega

-- **(b)** Prove the following theorem.
theorem quickSort_sorted (l : List ℕ) : Sorted (quickSort l) := by
  fun_induction quickSort with
  | case1 => exact Sorted.nil -- trivial case Sorted []
  | case2 pivot l ih_lo ih_hi =>
    -----------------------------------------------------
    --                     pivot
    --                      /
    --   □ □ □ □ □ □ □ □ □ ■ □ □ □ □ □ □
    --   └─────── < ─────┘   └─── ≥ ───┘
    --      |                        |
    -- case ➊: lower-half        case ➋: upper-half
    apply sorted_append
    ----------------------------------------------
    -- Case ➊, ➋ are sorted by definition
    · exact ih_lo
    · exact ih_hi
    ----------------------------------------------
    -- Case ➌ `pivot.MaxOfList (quickSort (lower pivot l))`
    -- pivot is larger than all lower-half elements `e`
    · intro e h
      simp_all [mem_quickSort]
      omega
    ----------------------------------------------
    -- Case ❹ `pivot.MinOfList (quickSort (upper pivot l))`
    · intro e h
      simp_all [mem_quickSort]

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
  fun_induction peak with
  -- case 1:  [mid + 1, hi] ⊆ [a, b]
  -- we just introduce some helpers so we can apply ih1
  | case1 =>
    expose_names
    have h1 : a ≤ mid + 1 := by omega
    have h2 : mid + 1 ≤ hi := by omega
    have h3 : f (mid + 1 - 1) < f (mid + 1) := by rw [Nat.add_sub_cancel]; exact h_1
    exact ih1 h1 h2 hhb (Or.inr h3) hhi
  -- case 2:  [lo, mid] ⊆ [a, b]
  -- identical idea for using ih2
  | case2 =>
    expose_names
    have h1 : lo ≤ mid := by omega
    have h2 : mid ≤ b := by omega
    have h3 : f (mid + 1) ≤ f mid := by omega
    exact ih1 hab h1 h2 hlo (Or.inr h3)
  -- case 3: IsPeak f a b lo
  | case3 =>
    expose_names
    unfold IsPeak
    -- no interval here since hi = lo
    have h_ : hi = lo := by omega
    rw [h_] at hhi
    -- then just show each formula case by case
    constructor
    -- goal 3.1: a ≤ lo
    · exact hab
    -- goal 3.2:
    -- lo ≤ b ∧ (lo = a ∨ f (lo - 1) ≤ f lo) ∧ (lo = b ∨ f (lo + 1) ≤ f lo)
    · constructor
      -- goal 3.2.1: lo ≤ b
      · omega
      -- goal 3.2.2: (lo = a ∨ f (lo - 1) ≤ f lo) ∧ (lo = b ∨ f (lo + 1) ≤ f lo)
      · exact ⟨hlo.imp_right Nat.le_of_lt, hhi⟩



-- **(b)** Prove the following theorem.
theorem peak_isPeak (f : ℕ → ℕ) (a b : ℕ) (hab : a ≤ b) : IsPeak f a b (peak f a b) := by
  -- for the peak we have lo = a and hi = b
  have h1 : a ≤ a := by omega
  have h2 : a ≤ b := hab
  have h3 : b ≤ b := by omega
  -- similarly, with lo := a and hi := b substituted into the inequalities
  have h4 : a = a ∨ f (a - 1) < f a := by left; rfl
  have h5 : b = b ∨ f (b + 1) ≤ f b := by left; rfl
  -- we can then apply the theorem directly
  exact peak_isPeak_of_invariant
    (f := f) (a := a) (b := b) (lo := a) (hi := b)
    (hab := h1) (hlh := h2) (hhb := h3)
    (hlo := h4) (hhi := h5)

-- **(c)** Prove the following theorem.
theorem peak_eq_of_unimodal (f : ℕ → ℕ) (a b m : ℕ) (ham : a ≤ m) (hmb : m ≤ b)
  (hinc : ∀ i, a ≤ i → i < m → f i < f (i + 1))
  (hdec : ∀ i, m ≤ i → i < b → f (i + 1) < f i) :
  peak f a b = m := by
  sorry

end HW6
