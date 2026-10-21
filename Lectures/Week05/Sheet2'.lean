/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


@[simp, grind] def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- How do define inductively of sortedness

-- inductive predicate
inductive Sorted : List ℕ → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t → Sorted (t) →  Sorted (a :: t)

-- introduction rules/constrtuctor
#check Sorted.single
#check Sorted.nil

-- # Example
example : Sorted [1] := by
  exact Sorted.single 1

#check Sorted.cons

-- # Example
example : Sorted [1,2,3] := by
  apply Sorted.cons
  · omega
  apply Sorted.cons
  · omega
  exact Sorted.single 3

-- # Example
example : ¬ Sorted [20,3,1] := by
  by_contra h
  cases h <;> expose_names
  · omega -- contradiction 20 ≤ 3
  · simp [Nat.MinOfList] at a_1  -- contradiction

-- # Example
example : ¬ Sorted [100,5,1] := by
  by_contra!
  cases this
  · omega
  simp at a_1

-- # Example
#check Sorted

-- Example: Proof by cases
theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by
  cases hxs
  · simp
  · simp only [Nat.MinOfList, List.mem_cons, forall_eq_or_imp]
    constructor
    · exact a_1
    · apply sorted_min at a_2
      exact fun a a_3 ↦ Nat.le_trans a_1 (a_2 a a_3)
  · exact a_1

-- # Exercise 5.1: Proof by induction
theorem sorted_min' {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by
  generalize h_eq : x :: xs = l
  replace hxs : Sorted l := by rwa [← h_eq]
  induction hxs generalizing xs x <;> expose_names
  · aesop
  · aesop
  · simp_all
    intro z hz
    have b_leq_z := a_ih z hz
    omega
  · simp_all

-- # Exercise 5.2
theorem sorted_is_preserved_by_min_cons {a : ℕ} {t : List ℕ} (hmin : a.MinOfList t) (ht : Sorted t) : Sorted (a :: t)
  := by exact Sorted.cons_min a t hmin ht

-- # Exercise 5.3
-- Define `merge` function that takes two sorted lists and ouputs a sorted list
-- merge [1, 5, 8] [2, 4, 9] = [1, 2, 4, 5, 8, 9]
-- merge [10,20] [] = [10, 20]
-- merge [2, 4, 4, 8] [1, 5, 8, 9] = [1, 2, 4, 4, 5, 8, 8, 9]

def merge : List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: merge xs (y::ys)
    else y :: merge (x :: xs) ys

lemma minOfList_merge {a : ℕ} {l1 l2 : List ℕ} (h1 : a.MinOfList l1) (h2 : a.MinOfList l2) :
  a.MinOfList (merge l1 l2) := by
    fun_induction merge l1 l2 <;> simp_all [Nat.MinOfList]

theorem sorted_is_preserved_by_merge {l1 l2 : List ℕ} (h1 : Sorted l1) (h2 : Sorted l2) :
  Sorted (merge l1 l2) := by
    fun_induction merge l1 l2 <;> expose_names
    · exact h1
    · exact h2
    · have hxs : Sorted xs := by
        cases h1 with
        | single => exact .nil
        | cons _ _ _ _ ht => exact ht
        | cons_min _ _ _ ht => exact ht
      have hmin2 : x.MinOfList (y :: ys) := by
        intro z hz
        simp only [List.mem_cons] at hz
        cases hz <;> expose_names
        · omega
        · exact Nat.le_trans h (sorted_min h2 z h_1)
      apply Sorted.cons_min
      · exact minOfList_merge (sorted_min h1) hmin2
      · exact ih1 hxs h2
    · have hys : Sorted ys := by
        cases h2 with
        | single => exact .nil
        | cons _ _ _ _ ht => exact ht
        | cons_min _ _ _ ht => exact ht
      have hmin1 : y.MinOfList (x :: xs) := by
        intro z hz
        simp only [List.mem_cons] at hz
        cases hz <;> expose_names
        · omega
        · exact Nat.le_trans (by omega) (sorted_min h1 z h_1)
      apply Sorted.cons_min
      · exact minOfList_merge hmin1 (sorted_min h2)
      · exact ih1 h1 hys
