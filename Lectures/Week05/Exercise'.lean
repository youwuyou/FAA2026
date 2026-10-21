/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

-- # Exercise: Define IsPalindrome
-- This should be true if and only if it can be read in forward and reverse direction
-- e.g., 'a', 'aba', 'aabbcbbaa'

inductive IsPalindrome {α : Type} : List α → Prop
  | nil : IsPalindrome []
  | single (a : α) : IsPalindrome [a]
  | cons_eq (a : α) (l : List α) : IsPalindrome l → IsPalindrome (a :: l ++ [a])

theorem IsPalindrome_imp_eq_reverse {α : Type} (l : List α) :
  IsPalindrome l → l = List.reverse l := by
  intro hl
  induction hl <;> expose_names
  · simp only [List.reverse_nil]
  · simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  · simp
    exact a_ih


-- We prove a strong helper lemma by induction over n : ℕ:
-- for all lists xs that satisfy xs = xs.reverse x, x is a palindrome.
lemma palindrome_helper {α : Type} : ∀ n : ℕ, ∀ xs : List α,
      xs.length ≤ n → xs = xs.reverse → IsPalindrome xs := by
    intro n
    induction n with
    | zero =>
        intro xs hlen hrev
        have hx : xs = [] := by
          simp [List.length_eq_zero_iff] at hlen
          exact hlen
        subst xs -- replace each occurrence of xs by []
        exact IsPalindrome.nil
    | succ n ih =>
        intro xs hlen hrev
        cases xs with
        | nil =>
            exact IsPalindrome.nil
        | cons a tail =>
            cases ht : tail.reverse with
          | nil =>
              have ht_nil : tail = [] := by
                rw [← List.reverse_reverse tail, ht]
                rfl
              subst tail
              exact IsPalindrome.single a
          | cons b middle =>
              have hcons : a :: tail = b :: (middle ++ [a]) := by
                simpa [List.reverse_cons, ht] using hrev
              have a_eq_b : a = b := by
                by_contra hcontra
                simp [hcontra] at hcons
              rw [← a_eq_b] at hcons
              rw [hcons]
              apply IsPalindrome.cons_eq a middle
              apply ih
              · simp [hcons] at hlen
                omega
              · simp [hcons] at hrev
                exact hrev

-- the theorem follows from the helper lemma
theorem IsPalindrome_pmi_eq_reverse {α : Type} (l : List α) :
  l = List.reverse l → IsPalindrome l := by
  intro h
  exact palindrome_helper l.length l (by rfl) h

-- more compact: bidirectional recursion
theorem IsPalindrome_pmi_eq_reverse' {α : Type} (l : List α) :
  l = List.reverse l → IsPalindrome l := by
  intro h
  induction l using List.bidirectionalRecOn with
  | H0 =>
      exact .nil
  | H1 a =>
      exact .single a
  | Hn a middle b ih =>
      rw [List.reverse_cons, List.reverse_append] at h
      rw [List.head_eq_of_cons_eq h.symm]
      apply IsPalindrome.cons_eq
      apply ih
      simp at h
      exact h.right.left


theorem IsPalindrome_reverse {α : Type} (l : List α) (h : IsPalindrome l) :
   IsPalindrome l.reverse  := by
   have eq_rev : l = l.reverse := IsPalindrome_imp_eq_reverse l h
   rw [← eq_rev]
   exact h

-- # Exercise: Binary Tree, Mirror and Complete Binary Tree
-- Define BinaryTree as follows
namespace mytree

inductive BinaryTree
  | nil
  | node (left : BinaryTree) (key : ℕ) (right : BinaryTree)

-- Define mirror operation as reversing the tree
def mirror : BinaryTree → BinaryTree
  | BinaryTree.nil        => BinaryTree.nil
  | BinaryTree.node l key r => BinaryTree.node (mirror r) key (mirror l)

--  Prove that mirror of mirror of a tree is the tree itself.
theorem mirror_mirror (t : BinaryTree) :
    mirror (mirror t) = t := by
    fun_induction mirror t
    · simp only [mirror]
    · simp only [mirror, ih1, ih2]

--  Prove that mirror of mirror of a tree is the tree itself.
theorem mirror_nil_iff (r : BinaryTree) : mirror r = BinaryTree.nil ↔ r = BinaryTree.nil := by
  fun_induction mirror r <;> simp

-- A binary tree is complete if every node has either two non-empty subtrees or two empty subtrees.
-- We can define it using inductive predicate as follows.

inductive Complete : BinaryTree  → Prop
  | leaf : Complete BinaryTree.nil
  | node  (l : BinaryTree) (key : ℕ) (r : BinaryTree)
      (hl : Complete l) (hr : Complete r)
      (hiff : l = BinaryTree.nil ↔ r = BinaryTree.nil) :
    Complete (BinaryTree.node l key r)

-- Prove that if t is complete then its mirroring is also complete.
theorem complete_mirror (t : BinaryTree) (ht : Complete t) :
    Complete (mirror t) := by
    induction ht <;> expose_names
    · unfold mirror
      exact Complete.leaf
    · unfold mirror
      apply Complete.node
      · exact hr_ih
      · exact hl_ih
      · rw [mirror_nil_iff, mirror_nil_iff]
        exact hiff.symm


end mytree
