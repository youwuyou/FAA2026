/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Lectures.Week06.API

set_option autoImplicit false
set_option tactic.hygienic false


-- Divid-and-Conquer + Functional Induction
-- In the recursive algorithms, we always break the problem P(n) into subproblems P(n₁) + P(n₂) of smaller instances
-- The correctness proof is typically based on induction from the smaller instances building up to the larger instance
-- In this lecture, we are going to see how functional induction formalizes this idea

-- Today, we are going to see two examples
-- 1. MergeSort
-- 2. Binary Search
-- The object of this lecture is to formulate
-- the correct intermediate hypothesis so that the functional induction goes through.


-- Merge sort
-- let's use the following version of merge

def Merge : List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

#check Merge

def list1 := [1,2,10]
def list2 := [3,5,20]

#eval Merge list1 list2

-- Define split list into two halves
-- List.take -- Extracts the first n elements of xs, or the whole list if n is greater than xs.length.
-- List.drop -- Removes the first n elements of the list xs. Returns the empty list if n is greater than the length of the list.
#check List.take
#eval [1,2,3,4,5].take 3
#check List.drop
#eval [1,2,3,4,5].drop 3

-- Merge sort
def MergeSort (x : List ℕ) : List ℕ  :=
if x.length < 2 then x
else
  let mid := x.length/2
  let l1 := x.take mid
  let l2 := x.drop mid
  let l1' := MergeSort l1
  let l2' := MergeSort l2
  Merge l1' l2'

-- Let's assume sorted_merge for now; we will prove sorted_merge in the next sheet
lemma minOfList_merge {a : ℕ} {l1 l2 : List ℕ} (h1 : a.MinOfList l1) (h2 : a.MinOfList l2)
  : a.MinOfList (Merge l1 l2) := by
    fun_induction Merge l1 l2 <;> simp_all [Nat.MinOfList]

theorem sorted_merge (l1 l2 : List ℕ) (hxs : Sorted l1) (hys : Sorted l2) : Sorted (Merge l1 l2) := by
  fun_induction Merge l1 l2 <;> expose_names
  · exact hxs
  · exact hys
  · have hxs' : Sorted xs := by
      cases hxs with
      | single => exact .nil
      | cons _ _ _ _ ht => exact ht
      | cons_min _ _ _ ht => exact ht
    have hmin : x.MinOfList (y :: ys) := by
      intro z hz
      simp only [List.mem_cons] at hz
      cases hz <;> expose_names
      · omega
      · trans y
        · exact h
        · exact sorted_min hys z h_1
    apply Sorted.cons_min
    · apply minOfList_merge
      · exact sorted_min hxs
      · exact hmin
    · exact ih1 hxs' hys
  · have hys' : Sorted ys := by
      cases hys with
      | single => exact .nil
      | cons _ _ _ _ ht => exact ht
      | cons_min _ _ _ ht => exact ht
    have hmin : y.MinOfList (x :: xs) := by
      intro z hz
      simp only [List.mem_cons] at hz
      cases hz <;> expose_names
      · omega
      · trans x
        · omega
        · exact sorted_min hxs z h_1
    apply Sorted.cons_min
    · apply minOfList_merge
      · exact hmin
      · exact sorted_min hys
    · exact ih1 hxs hys'

#check MergeSort.induct

-- Exercise 1.1: use sorted_merge theorem to prove that MergeSort outputs a sorted list
theorem MS_Sorted (xs : List ℕ) : Sorted (MergeSort xs) := by
  fun_induction MergeSort
  · cases x
    · exact Sorted.nil
    · simp_all only [List.length_cons, Order.lt_two_iff, add_le_iff_nonpos_left,
      nonpos_iff_eq_zero, List.length_eq_zero_iff]
      exact Sorted.single head
  · exact sorted_merge l1' l2' ih2 ih1
