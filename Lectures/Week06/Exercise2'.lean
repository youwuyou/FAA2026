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
    simp [Sorted.nil, Sorted2.nil]
  | x::[] => -- base case 2: singleton list
    simp [Sorted.single, Sorted2.single]
  | x::y::t => -- recursive case: list of size ≥ 2
    constructor
    · intro sorted2
      cases sorted2 -- only one case as the list has size ≥ 2
      · expose_names
        apply Sorted.cons
        · exact a_1
        · apply sorted2_helper.1 a_2 -- recursive call
    · intro sorted
      cases sorted <;> expose_names
      · apply Sorted2.cons
        · exact a_1
        · apply sorted2_helper.2 a_2 -- recursive call
      · apply Sorted2.cons
        · simp [Nat.MinOfList] at a_1
          omega
        · apply sorted2_helper.2 a_2 -- recursive call

-- Prove using `induction`
lemma sorted2_helper' {l : List ℕ} : Sorted2 l ↔ Sorted l := by
  induction l <;> expose_names
  · simp [Sorted.nil, Sorted2.nil]
  · constructor
    · intro sorted2
      cases sorted2 <;> expose_names
      · exact Sorted.single head
      · have sorted_tail : Sorted (b :: t) := tail_ih.1 a_2
        apply Sorted.cons
        · exact a_1
        · exact sorted_tail
    · intro sorted
      cases sorted <;> expose_names
      · exact Sorted2.single head
      · have sorted_tail : Sorted2 (b :: t) := tail_ih.2 a_2
        apply Sorted2.cons
        · exact a_1
        · exact sorted_tail
      · have sorted_tail : Sorted2 tail := tail_ih.2 a_2
        match tail with
        | [] =>
          exact Sorted2.single head
        | b::bs =>
          apply Sorted2.cons
          · simp [Nat.MinOfList] at a_1
            exact a_1.left
          · exact sorted_tail

-- Hint: use `ext`
theorem sorted_eq_sorted2 : Sorted2 = Sorted := by
  ext l
  exact sorted2_helper

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
  induction hl <;> expose_names
  · simp
  · simp
  · simp [a_ih]
    constructor
    · exact a_1
    · intro x hx
      grw [a_1]
      simp at a_ih
      apply a_ih.1
      exact hx
  · simp [a_ih] -- can also use `simp [*]` to simplify using all hypotheses
    simp [Nat.MinOfList] at a_1
    exact a_1

lemma pairwise_sorted {l : List ℕ} (hl : List.Pairwise (· ≤ ·) l) : Sorted l := by
  induction l <;> expose_names
  · exact Sorted.nil
  · simp at hl
    obtain ⟨head_min, pairwise_tail⟩ := hl
    apply Sorted.cons_min
    · unfold Nat.MinOfList
      exact head_min
    · apply tail_ih
      exact pairwise_tail

lemma sorted_pairwise' {l : List ℕ} (hl : Sorted l) : List.Pairwise (· ≤ ·) l := by
  cases hl <;> expose_names
  · simp
  · simp
  · have hrec : List.Pairwise (· ≤ ·) (b :: t) := sorted_pairwise a_2 -- recursive call
    simp [hrec]
    constructor
    · exact a_1
    · intro x hx
      grw [a_1]
      simp at hrec
      apply hrec.1
      exact hx
  · have hrec : List.Pairwise (· ≤ ·) t := sorted_pairwise a_2 -- recursive call
    simp [hrec]
    simp [Nat.MinOfList] at a_1
    exact a_1

lemma pairwise_sorted' {l : List ℕ} (hl : List.Pairwise (· ≤ ·) l) : Sorted l := by
  cases l <;> expose_names
  · exact Sorted.nil
  · simp at hl
    obtain ⟨head_min, pairwise_tail⟩ := hl
    apply Sorted.cons_min
    · unfold Nat.MinOfList
      exact head_min
    · apply pairwise_sorted' -- recursive call
      exact pairwise_tail

-- Hint: use `ext`
theorem sorted_eq_pairwise : List.Pairwise (· ≤ ·) = Sorted := by
  ext l
  exact Iff.intro pairwise_sorted sorted_pairwise
