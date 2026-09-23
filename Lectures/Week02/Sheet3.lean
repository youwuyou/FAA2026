/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

/-! New tactics
 * `left`  -- change the goal of the form P ∨ Q to P
 * `right` -- change the goal of the form P ∨ Q to Q
 * `cases` -- deal with cases.
              That is, if you have h: P ∨ Q then cases h will automatically split into two goals.
              One goal assume P and the other goal assume Q.
 * `by_cases` -- prove by cases
-/

open Set
variable {α : Type*}
variable (A B C D : Set α)

-- Example: Left/Right tactics
example : A ⊆ A ∪ B := by
  rw [subset_def]
  intro x hx
  rw [mem_union]
  left
  exact hx

-- Example: by_cases tactics
example (x : α) : x ∈ A ∨ x ∉ A := by
  by_cases h : x ∈ A
  · left; exact h
  · right; exact h

-- Example: cases tactics
example : ∀ x ∈ A ∪ B, x ∈ A ∪ B ∪ C:= by
  intro x hx
  rw [mem_union] at hx
  cases hx
  · rw [mem_union]
    left
    rw [mem_union]
    left
    exact h
  · left
    right
    exact h

-- Exercise 3: Cases tactics. You are allowed to use *only* these two lemmas.
#check mem_union
#check subset_def

lemma my_union_subset_imp :  A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C := by
  intro ⟨h_AC, h_BC⟩
  rw [subset_def]
  intro x h_AB
  rw [mem_union] at h_AB
  cases h_AB with
  | inl ha => exact h_AC ha
  | inr hb => exact h_BC hb

-- Extend my_union_subset_imp to my_union_subset_iff
-- You are allowed to use *only* these two lemmas.
#check mem_union
#check subset_def

-- running example
lemma my_union_subset_iff :  A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  constructor
  -- subgoal 1: A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C
  · intro a
    exact my_union_subset_imp A B C a
  -- subgoal 2: A ∪ B ⊆ C → A ⊆ C ∧ B ⊆ C
  · intro lhs
    constructor
    -- subsubgoal 2.1: A ⊆ C
    · rw [subset_def]
      intro x hx
      apply lhs
      left -- union is same as OR, we take left part
      exact hx
    -- subsubgoal 2.1: B ⊆ C
    · rw [subset_def]
      intro x hx
      apply lhs
      rw [mem_union]
      right
      exact hx

-- Exercise 4: you may want to use my_union_subset_iff
example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
  intro h1 h2 x h
  rw [mem_union] at h
  cases h with
  | inl hb => exact h1 hb
  | inr hc => exact h2 hc


/-! New tactics
 * `ext`  -- extensionality. Proving that two functions are identical.
  Since sets are functions in Lean,
  `ext` can be used to prove set equality.
-/

-- example
lemma inter_comm : A ∩ B = B ∩ A := by
  ext x
  constructor
  -- subgoal 1: x ∈ A ∩ B → x ∈ B ∩ A
  · intro a
    rw [mem_inter_iff]
    rw [mem_inter_iff] at a
    obtain ⟨ha,hb⟩ := a
    exact ⟨hb,ha⟩
  -- subgoal 2: x ∈ B ∩ A → x ∈ A ∩ B
  · intro lhs
    rw [mem_inter_iff]
    rw [mem_inter_iff] at lhs
    obtain ⟨left, right⟩ := lhs
    exact And.intro right left

-- example
lemma absorption_law : A ∩ (A ∪ B) = A := by
  ext x
  constructor
  · intro
    rw [mem_inter_iff] at a
    obtain ⟨ha,hb⟩ := a
    assumption
  · intro
    constructor
    · exact a
    · left
      exact a

-- Exercise 5
lemma union_comm : A ∪ B = B ∪ A := by
  ext x
  rw [union_def]
  rw [union_def]
  constructor
  -- subgoal 1: x ∈ A ∪ B → x ∈ B ∪ A
  · intro lhs
    cases lhs with
    | inl ha => right; exact ha
    | inr hb => left; exact hb
  -- subgoal 2: x ∈ B ∪ A → x ∈ A ∪ B
  · intro lhs
    cases lhs with
    | inl hb => right; exact hb
    | inr ha => left; exact ha
