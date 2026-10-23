/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- # Challenges in applying functional induction to divide-and-conquer algorithms
-- Sometimes, we cannot immediately call funtional induction even though the algoithm is recursive.
-- This is usually because the hypothesis is too specialized.
-- The key idea is to formulate a more `general inductive hypothesis`

-- In this sheet, we walk through binary search on a sorted array as an example

-- Consider the following formulation of the sorted array
-- This version has fewer proof obligations
-- because we don't have to worry about the indices (out-of-bounds).
-- This allows us to focus on writing proofs rather than dealing with low-level proof obligations.

structure SortedArrayFun (n : ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

#check SortedArrayFun
#check SortedArrayFun.get
#check SortedArrayFun.sorted
-- A function f is monotone if a ≤ b implies f a ≤ f b.
#check Monotone

def contains_bs {n : ℕ} (arr : SortedArrayFun n) (q : ℕ) : Option ℕ :=
  bs_aux 0 (n-1)
  where bs_aux (a b :ℕ) (h: a ≤ b := by omega): Option ℕ  :=
  if h: a = b then
    if q = arr.get a then some a
    else none
  else
    let mid := (a+b)/(2 : ℕ )
    if      q < arr.get mid then bs_aux a mid
    else if  arr.get mid < q then bs_aux (mid+1) b
    else some mid


theorem subinterval_to_interval_qlt {n : ℕ} (arr : SortedArrayFun n) (q a mid b : ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b) -- [[a q⁻¹ mid] b]:
  (h_q : q < arr.get mid) :
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, a ≤ i ∧ i ≤ mid ∧ arr.get i = q) := by
  constructor
  · -- cleaning up
    intro h
    obtain ⟨i,hi⟩ := h
    use i
    suffices i ≤ mid by grind
    replace hi: arr.get i = q := by grind
    -- the rest of the proof follows from one important fact: Monotone arr.get
    have: Monotone arr.get := by exact arr.sorted
    simp [Monotone] at this
    by_contra h
    have h_mid_i : mid ≤ i := by omega
    have h_get : arr.get mid ≤ arr.get i := this h_mid_i
    omega
  · -- easy direction
    intro h
    cases h
    use w
    grind

-- The property is: "Searching in [a, b] returns q if and only if q can be found from an index in [a,b]."
#check contains_bs.bs_aux
lemma bs_aux_correctness (n q : ℕ) (arr : SortedArrayFun n) (a b : ℕ) (h_le : a ≤ b) :
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (contains_bs.bs_aux arr q a b h_le ≠ none) := by
    fun_induction contains_bs.bs_aux
    · -- base case 1
      simp_all only [Std.le_refl, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
      use b_1
    · -- base case 2
      grind
    · -- go left
      rw [← ih1]
      apply subinterval_to_interval_qlt
      · grind
      · grind
    · -- go right; symmetric case
      rw [← ih1]
      constructor
      · intro h
        obtain ⟨i, hi⟩ := h
        use i
        suffices mid + 1 ≤ i by grind
        replace hi : arr.get i = q := by grind
        by_contra h'
        have h_i_mid : i ≤ mid := by omega
        have h_get : arr.get i ≤ arr.get mid := arr.sorted h_i_mid
        omega
      · intro h
        obtain ⟨i, hi⟩ := h
        use i
        grind
    · -- found it
      simp_all only [not_lt, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
      use mid
      grind


theorem contains_bs_correctness (n q : ℕ) (h : 0 < n) (arr : SortedArrayFun n) :
  (∃ i, i < n ∧ arr.get i = q) ↔ (contains_bs arr q ≠ none) := by
  unfold contains_bs
  have := bs_aux_correctness n q arr 0 (n-1)
  grind

/-
-- Hints below
-/

-- Exercise: Fill in the rest
theorem subinterval_to_interval_qgt {n : ℕ} (arr : SortedArrayFun n) (q a mid b: ℕ)
  (h_bounds : a ≤ mid ∧ mid ≤ b)  -- [a [mid q⁻¹ b]]:
  (h_q: arr.get mid < q ):
  (∃ i, a ≤ i ∧ i ≤ b ∧ arr.get i = q) ↔ (∃ i, (mid+1) ≤ i ∧ i ≤ b ∧ arr.get i = q)  := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h
    use i
    suffices mid + 1 ≤ i by grind
    replace hi : arr.get i = q := by grind
    by_contra h'
    have h_i_mid : i ≤ mid := by omega
    have h_get : arr.get i ≤ arr.get mid := arr.sorted h_i_mid
    omega
  · intro h
    obtain ⟨i, hi⟩ := h
    use i
    grind


/- Follow-up Exercise:
  Step (1) finish the remaining proofs posslby with grind.
  Step (2) then write a full proof without grind. -/
