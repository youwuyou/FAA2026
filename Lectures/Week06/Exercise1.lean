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

theorem sorted_sublist (y : ℕ) (ys : List ℕ) (h : sorted (y :: ys)) : Nat.leqAll y ys ∧ sorted ys := sorry

theorem sorted_xyys_of_sorted_yys (x y : ℕ) (ys : List ℕ) (h_1 : x ≤ y) (h : sorted (y :: ys)) :
  sorted (x :: y :: ys) := sorry

theorem sorted_y_insert (x y : ℕ) (ys : List ℕ) (h_1 : y < x) (h2 : sorted (insert x ys))
  (h : Nat.leqAll y ys) : sorted (y :: insert x ys) := sorry

lemma insert_into_sorted ( x : ℕ) (xs : List ℕ) (h : sorted xs) : sorted (insert x xs) := sorry

-- Let's prove that insertion sort is sorted.
theorem IS_sorted (xs : List ℕ) : sorted (IS xs) := by sorry

end mysorting
