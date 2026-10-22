/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import waterfall

namespace mysorting

-- Define Insertion Sort
def insert (x : ℕ) (xs : List ℕ) : List ℕ :=
  match xs with
  | [] => [x]
  | y :: ys =>
    if x ≤ y then x :: xs
    else y :: insert x ys

def IS : List ℕ → List ℕ
 | [] => []
 | x :: xs =>
 let ret := IS xs
 insert x ret

#eval IS [5,10,2,3,9]
-- Let's state a sorted property using type

@[simp] abbrev Nat.leqAll (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- Property of sortedness
inductive sorted : List ℕ → Prop
| empty : sorted []
| min (a : ℕ ) (t : List ℕ) : Nat.leqAll a t → sorted t → sorted (a :: t)

-- In this exercise, you are asked to prove that insertion sort returns a sorted list.
-- Complete all the proofs below *without* using grind and waterfall.

theorem sorted_sublist (y : ℕ) (ys : List ℕ) (h : sorted (y :: ys)) : Nat.leqAll y ys ∧ sorted ys := by
  cases h
  expose_names
  exact ⟨h_1, h⟩

theorem sorted_xyys_of_sorted_yys (x y : ℕ) (ys : List ℕ) (h_1 : x ≤ y) (h : sorted (y :: ys)) :
  sorted (x :: y :: ys) := by
  apply sorted_sublist at h
  apply sorted.min
  simp_all only [Nat.leqAll, List.mem_cons, forall_eq_or_imp, true_and]
  intro a ha
  obtain ⟨h,_⟩ := h
  have: y ≤ a := by simp_all
  exact Nat.le_trans h_1 (h a ha)
  exact sorted.min y ys h.1 h.2

theorem sorted_y_insert (x y : ℕ) (ys : List ℕ) (h_1 : y < x) (h2 : sorted (insert x ys))
  (h : Nat.leqAll y ys) : sorted (y :: insert x ys) := by
  fun_induction insert
  · simp_all only [Nat.leqAll, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    refine sorted_xyys_of_sorted_yys y x [] (by omega) h2
  · expose_names
    refine sorted_xyys_of_sorted_yys y x (y_1 :: ys) (by omega) h2
  · expose_names
    refine sorted_xyys_of_sorted_yys y y_1 (insert x ys) ?_ h2
    simp_all

lemma insert_into_sorted ( x : ℕ) (xs : List ℕ) (h : sorted xs) : sorted (insert x xs) := by
  fun_induction insert
  · apply sorted.min
    · simp
    · exact sorted.empty
  · expose_names
    exact sorted_xyys_of_sorted_yys x y ys h_1 h
  · expose_names
    apply sorted_sublist at h
    simp_all only [not_le, forall_const]
    refine sorted_y_insert x y ys h_1 ih1 h.1

-- Let's prove that insertion sort is sorted.
theorem IS_sorted (xs : List ℕ) : sorted (IS xs) := by
  fun_induction IS
  · exact sorted.empty
  · expose_names
    exact insert_into_sorted y (IS ys) ih1

end mysorting
