/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Exercise File for Week 2
-- Additional instruction: for every problem, you must supply an informal proof before a Lean proof.
-/

/-
  Recall that sets are defined through membership predicates in Lean
-/
def Set' (α : Type) := α → Prop

namespace Set

variable {α : Type} (A B C : Set α)

/-
# Information
You are allowed to use the following tactics:
  `intro`, `ext`, `exact`, `apply`, `cases`, `obtain`, `left`, `right`, `expose_names`,
  `constructor`, `rewrite`, `rw`, `have`, `rfl`, `assumption` and `contradiction`.
You are also allowed to use local definitions using `let`.
-/

/-
## Hints on using obtain
You can use `obtain` for destructuring conjunctions and existential propositions.
-- For `h : P ∧ Q`, you can write `obtain ⟨hp, hq⟩` to obtain `hp : P` and `hq : Q`
-- For `h : ∃ k : ℕ, P k`, you can write `obtain ⟨k, hk⟩` to obtain `k : ℕ` and `hk : P k`
-/
example (P Q : Prop) (h : P ∧ Q) : P := by
  obtain ⟨hp, hq⟩ := h -- hp : P, hq : Q
  exact hp

example (h : ∃ k : ℕ, k + 1 = 42) : ∃ k : ℕ, k + 1 = 43 := by
  obtain ⟨k, hk⟩ := h -- k : ℕ, hk : k+1 = 42
  use k+1
  rw [hk]

/-
## Hints on using cases
`cases h` eliminates the original hypothesis `h : P ∨ Q` and replaces it in each branch
with a proof of `P` or `Q`. These new proofs may initially have inaccessible names;
`expose_names` makes them usable, you can check the name in the InfoView (often is `h`).
Pattern matching lets you choose clear names such as `hP` and `hQ`.
-/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  · right
    assumption
  · left
    assumption

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h <;> expose_names
  · right
    exact h
  · left
    exact h

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP =>
    right
    exact hP
  | inr hQ =>
    left
    exact hQ


/-
  Exercise 1:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.
-/
theorem Q1 : (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := by
  -- my informal idea: we need a bidirectional implication, w.l.o.g
  -- we discuss for subgoal 1 that:
  -- x ∈ (A ∩ B) ∪ C ↔ x ∈ (A ∩ B) ∨ (x ∈ C)
  -- then we need to do a lot of case distinctions, which we
  -- clarify in the following
  ext x
  constructor
  -- subgoal 1: x ∈ (A ∩ B) ∪ C → x ∈ (A ∪ C) ∩ (B ∪ C)
  · intro lhs
    -- we need to split case because x may land on either parts
    cases lhs with
    -- case 1.1: assume x ∈ (A ∩ B)
    | inl hab =>
      obtain ⟨ha, hb⟩ := hab
      exact ⟨Or.inl ha, Or.inl hb⟩
    -- case 1.2: assume x ∈ C
    | inr hc =>
      exact ⟨Or.inr hc, Or.inr hc⟩
  -- subgoal 2: x ∈ (A ∪ C) ∩ (B ∪ C) → x ∈ (A ∩ B) ∪ C
  · intro lhs
    obtain ⟨hac, hbc⟩ := lhs
    -- here w.l.o.g we enter case distinction of x ∈ A ∪ C first
    cases hac with
    -- if x ∈ A, we further leverage the fact that x ∈ B ∪ C holds
    | inl ha =>
      cases hbc with
      | inl hb =>
        left
        exact And.intro ha hb
      | inr hc => right; exact hc
    -- if x ∈ C, we are done
    | inr hc => right; exact hc

/-
  We define the operation of the symmetric difference on sets.
-/
def symm_diff (A B : Set α) : Set α :=
  (A \ B) ∪ (B \ A)

notation A " ∆ " B => Set.symm_diff A B

#check symm_diff

/-
  Exercise 2:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.
-/
theorem Q2 (x : α) : x ∈ A ∩ (B ∆ C) → x ∈ (A ∩ B) ∆ (A ∩ C) := by
  -- TODO: I still need to add the informal proof
  intro lhs
  obtain ⟨ha, hbc⟩ := lhs
  -- rw [symm_diff]
  -- rw [symm_diff] at hbc
  cases hbc with
  | inl hb_diff =>
    left
    obtain ⟨hb, hnc⟩ := hb_diff
    constructor
    -- subgoal 1.1: x ∈ A ∩ B
    · exact ⟨ha, hb⟩
    -- subgoal 1.2: x ∉ A ∩ C
    · by_contra
      obtain ⟨_, hc⟩ := this
      contradiction
  | inr hc_diff =>
    right
    obtain ⟨hc, hnb⟩ := hc_diff
    constructor
    -- subgoal 2.1: x ∈ A ∩ C
    · exact ⟨ha, hc⟩
    -- subgoal 2.2: x ∉ A ∩ B
    · by_contra
      obtain ⟨ha, hb⟩ := this
      contradiction

/-
  Exercise 3:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.

  Hint: the following theorems may be helpful.
-/
#check Set.mem_union
#check Set.mem_inter
#check Set.mem_sdiff
#check Set.mem_compl_iff
#check Set.notMem_compl_iff
#check Iff.mp
#check Iff.mpr

theorem Q3 : (A ∆ B) = Aᶜ ∆ Bᶜ := by
  sorry


/-!
  Exercise 4:

  Prove the following theorems.
  You may only use the tactics stated at the start of the sheet.
  You can use Q4a and Q4b for Q4c, even if you have not proven them.
-/

-- The following theorems may be helpful
#check empty_sdiff
#check empty_inter
#check empty_union

#check sdiff_empty
#check inter_empty
#check union_empty

#check sdiff_self
#check inter_self
#check union_self

-- You can use also the following theorem
theorem symm_diff_assoc : ((A ∆ B) ∆ C) = (A ∆ (B ∆ C)) := by
  unfold symm_diff
  grind -- `grind` is a powerful tactic, but you are not allowed to use it yet


theorem Q4a : (∅ ∆ A) = A := by
  sorry

theorem Q4b : (A ∆ A) = ∅ := by
  sorry

theorem Q4c : ∀ A : Set ℕ, ∀ B : Set ℕ, ∃ C : Set ℕ, (A ∆ C) = B := by
  sorry

end Set

namespace Asymptotics

/-
  Consider the following definition of big-O-notation.
-/
def inBigO (f g : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, f n ≤ c * g n

def BigO (g : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {f : ℕ → ℕ | inBigO f g}

notation "O(" g ")" => BigO g

#check inBigO
#check BigO

/-
  Hint: The following theorems may be helpful.
-/
#check Set.mem_ofPred_eq
#check zero_lt_one
#check one_mul

/-
  Exercise 5:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.
-/
theorem Q5 (g : ℕ → ℕ) : g ∈ O(g) := by
  sorry

end Asymptotics
