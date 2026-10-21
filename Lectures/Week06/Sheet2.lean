/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Lectures.Week06.API
import Waterfall

set_option autoImplicit false
set_option tactic.hygienic false

-- In this sheet, we are going to prove the merge lemma
def Merge : List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

theorem min_all_merge (x : ℕ) (xs ys : List ℕ) (hxs : x.MinOfList xs) (hys : x.MinOfList ys)
  : x.MinOfList (Merge xs ys) := by waterfall

-- We did in the previous lectures.
theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs))
  : Sorted xs := by waterfall

#check sorted_min

theorem sorted_merge (l1 l2 : List ℕ) (hxs : Sorted l1) (hys : Sorted l2) : Sorted (Merge l1 l2) := by
  fun_induction Merge
  · assumption
  · assumption
  · apply Sorted.cons_min
    · apply sorted_min at hxs
      apply sorted_min at hys
      suffices x.MinOfList (y::ys) by
        exact min_all_merge x xs (y :: ys) hxs this
      simp_all only [Nat.MinOfList, List.mem_cons, forall_eq_or_imp, true_and]
      exact fun a a_1 ↦ Nat.le_trans h (hys a a_1)
    · exact ih1 (sorted_suffix hxs) hys
  · -- Exercise 2.1
    sorry

-- Exercise 2.2
theorem merge_min_out_sym(x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y)
  (h_min_in_ys : ∀ y ∈ ys, x ≤ y) : Merge ys (x ::xs)  = x :: Merge ys xs := by sorry

-- Exercise 2.3: Prove this without using grind/waterfall
example (l1 l2 : List ℕ) : (Merge l1 l2).length = l1.length + l2.length  := by sorry
