/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


@[simp, grind] def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y


inductive Sorted : List ℕ → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t → Sorted (t) →  Sorted (a :: t)

inductive Sorted2 : List ℕ → Prop
  | nil : Sorted2 []
  | single (a : ℕ) : Sorted2 [a]
  | cons (a b : ℕ ) (t : List ℕ ) : a ≤ b → Sorted2 (b :: t) → Sorted2 (a :: b :: t)

/-!
  **Task A**
  Prove that Sorted2 = Sorted.
-/

-- Prove without `induction` (match/cases + recursive calls)
lemma sorted2_helper {l : List ℕ} : Sorted2 l ↔ Sorted l := by
  match l with
  | []   => -- base case 1: empty list
    sorry
  | x::[] => -- base case 2: singleton list
    sorry
  | x::y::t => -- recursive case: list of size ≥ 2
    sorry

-- Prove using `induction`
lemma sorted2_helper' {l : List ℕ} : Sorted2 l ↔ Sorted l := by
  induction l <;> expose_names
  · sorry
  · sorry

-- Hint: use `ext`
theorem sorted_eq_sorted2 : Sorted2 = Sorted := by
  sorry

/-!
  **Task B**
  Prove that List.Pairwise (· ≤ ·) = Sorted.
-/

-- This is how List.Pairwise is defined
inductive Pairwise' {α : Type} (P : α → α → Prop) : List α → Prop
| nil : Pairwise' P []
| cons (head : α) (tail : List α) :
  (∀ x : α, x ∈ tail → P head x) → (Pairwise' P tail) → Pairwise' P (head :: tail)


lemma sorted_pairwise {l : List ℕ} (hl : Sorted l) : List.Pairwise (· ≤ ·) l := by
  sorry

lemma pairwise_sorted {l : List ℕ} (hl : List.Pairwise (· ≤ ·) l) : Sorted l := by
  sorry

-- Hint: use `ext`
theorem sorted_eq_pairwise : List.Pairwise (· ≤ ·) = Sorted := by
  sorry
