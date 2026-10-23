/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false

/-!
# Homework File for Week 5

There are 5 exercises. Each correctly solved exercise is worth 20 points.

All tactics **except `grind`** are welcome. However, if you use `grind`
in an exercise, you can still get up to half the points.

We also reserve the right to subtract points for unreadable code.
Please use the code style used in the lecture. If you deviate from it,
please explain why and what the code does in the comments.
-/

@[simp] def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y
@[simp] def Nat.MaxOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≥ y

namespace HW5

/-!
  **Exercise 1**

  First fill in the definition of the `rename` function, then prove the theorem below.
-/
inductive RegEx (α : Type) where
  | epsilon : RegEx α
  | symbol (a : α) : RegEx α
  | choice (r1 r2 : RegEx α) : RegEx α
  | concat (r1 r2 : RegEx α) : RegEx α
  | star (r : RegEx α) : RegEx α

inductive Matches {α : Type} : RegEx α → List α → Prop where
  -- `epsilon` matches the empty word, i.e. empty list
  | epsilon : Matches .epsilon []
  -- `symbol a` matches the singleton list `[a]`
  | symbol (a : α) : Matches (.symbol a) [a]
  ------------------------------------------------------------
  -- **MyNote:** in the following are rules in the form that
  -- `Matches r1 w = regex r1 matches word w`
  ------------------------------------------------------------
  -- If `r1` matches a word `w`, then `choice r1 r2` matches `w`
  | choice_left {r1 r2 : RegEx α} {w : List α} :
      Matches r1 w → Matches (.choice r1 r2) w
  -- If `r2` matches a word `w`, then `choice r1 r2` matches `w`
  | choice_right {r1 r2 : RegEx α} {w : List α} :
      Matches r2 w → Matches (.choice r1 r2) w
  -- If `r1` and `r2` match the words `w1` and `w2`, respectively,
  -- then `concat r1 r2` matches `w1 ++ w2`
  | concat {r1 r2 : RegEx α} {w1 w2 : List α} :
      Matches r1 w1 → Matches r2 w2 → Matches (.concat r1 r2) (w1 ++ w2)
  -- Star base case: `star r` matches the empty word
  | star_nil (r : RegEx α) : Matches (.star r) []
  -- Star recursive case: If `r` matches `w1` and `star r` matches `w2`,
  -- then `star r` matches `w1 ++ w2`
  | star_more {r : RegEx α} {w1 w2 : List α} :
      Matches r w1 → Matches (.star r) w2 → Matches (.star r) (w1 ++ w2)

-- **(a)** Fill in the definition of the rename function, which should
-- replace every `a : α` by `f a : β`.
-- *MyQuestion:* it seems like we need to repeat a lot here for choice, concat, star
-- although they just follow the simple pattern of composing functions. Is there a way
-- to avoid repeating the code here?
def rename {α β : Type} (f : α → β) : RegEx α → RegEx β
  -- base cases: epsilon is special so no rename, then
  | RegEx.epsilon => RegEx.epsilon
  | RegEx.symbol a => RegEx.symbol (f a)
  -- composite cases: rename each argument using `rename f` and then use definitions
  | RegEx.choice r1 r2 => RegEx.choice (rename f r1) (rename f r2)
  | RegEx.concat r1 r2 => RegEx.concat (rename f r1) (rename f r2)
  | RegEx.star r => RegEx.star (rename f r)

-- **(b)** Prove the following theorem.
theorem matches_rename {α β : Type} (f : α → β) {r : RegEx α} {w : List α}
  (h : Matches r w) : Matches (rename f r) (List.map f w) := by
  -- overall goal: to show `Matches (rename f r) (List.map f w)`
  induction h with
  -- 1. epsilon: here no renaming was used so trivially proved
  |  epsilon => exact Matches.epsilon
  -- 2. symbol: here the symbol is renamed, we take the renaming rule `f` and again match
  |  symbol a => exact Matches.symbol (f a)
  ------------------------------------------------
  -- 3. choice_left, choice_right; here we shall see
  -- the overall goal can be rewritten by definitions of choice_left/right
  -- then the inductive hypothesis can be applied directly.
  |  choice_left h ih =>
    expose_names
    -- now we see the inductive hypothesis is:
    -- `ih : Matches (rename f r1) (List.map f w_1)`
    -- rewriting the goal with definition, we can then apply
    apply Matches.choice_left
    exact ih
  |  choice_right h ih =>
    expose_names
    apply Matches.choice_right
    exact ih
  ----------------------------------------------
  -- 4. concat
  |  concat h h2 ih ih2 =>
    expose_names
    rw [List.map_append, rename]
    -- now we see the patterns match so can use both inductive hypotheses
    exact Matches.concat ih ih2
  ----------------------------------------------
  -- 5. star: repeats an expression zero or more times
  -- 5.1 repeats zero time
  |  star_nil a =>
    exact Matches.star_nil (rename f a)
  -- 5.2 repeats more times
  |  star_more ih ih2 ih3 ih4 =>
    expose_names
    -- simp?
    simp only [List.map_append]
    -- goal becomes
    -- `Matches (rename f r_1.star) (List.map f w1 ++ List.map f w2)`
    exact Matches.star_more ih3 ih4

/-!
  **Exercise 2**

  Prove the following theorem by induction over the predicate.

  Hint: the `split` tactic is useful for if-else splits.
-/
inductive BinaryTree where
  | nil
  | node (value : ℕ) (left : BinaryTree) (right : BinaryTree)

def inorder : BinaryTree → List ℕ
  | .nil => []
  | .node value l r => inorder l ++ value :: inorder r

inductive IsBST : BinaryTree → Prop where
  | nil : IsBST .nil
  | node (value : ℕ) (l : BinaryTree) (r : BinaryTree)
      (bst_left : IsBST l) (bst_right : IsBST r)
      (hleft : ∀ x ∈ inorder l, x < value)
      (hright : ∀ x ∈ inorder r, value < x) :
      IsBST (.node value l r)

def lookup (q : ℕ) : BinaryTree → Bool
  | .nil => false
  | .node value l r =>
      if q < value then lookup q l
      else if value < q then lookup q r
      else true

-- **MyQuestion:** Am I doing anything wrong? This proof is absurdly long??
-- I think I perhaps miss some useful tactics that I should use here instead
theorem lookup_correct (q : ℕ) {t : BinaryTree} (ht : IsBST t) :
  lookup q t = true ↔ q ∈ inorder t := by
  induction ht with
  -- subgoal 1: `lookup q BinaryTree.nil = true ↔ q ∈ inorder BinaryTree.nil`
  | nil =>
    simp only [lookup, inorder]
    -- break down into two cases to show
    -- both are trivially contradictory assumptions
    constructor
    -- case 1.1: false = true → q ∈ []
    -- case 1.2: q ∈ [] → false = true
    · intro h; contradiction
    · intro h; contradiction
  -------------------------------------------
  -- subgoal 2:
  --   lookup q (BinaryTree.node value l r) = true
  -- ↔ q ∈ inorder (BinaryTree.node value l r)
  | node =>
    expose_names
    constructor
    -- (→) direction
    · intro h
      simp_all only [inorder, List.mem_append, List.mem_cons]
      -- **MyNotes:**
      ----------- REWRITING GOAL ------------------------------------
      -- either ➊ q ∈ inorder l
      -- or ➋ q = value
      -- or ➌ q ∈ inorder r
      rw [lookup] at h
      ----------- CASE SPLIT ASSUMPTIONS ----------------------------
      -- Here I used `split_ifs` from the provided cheatsheet
      -- https://leanprover-community.github.io/papers/lean-tactics.pdf
      -- I tried cases h, by_cases etc., but found them not very satisfying
      -- so I use the one from cheatsheet now.
      -------------------------------------------------------------------
      -- case for (q ∈ inorder l) ∨ (q = value ∨ q ∈ inorder r)
      --               |               |                  |
      --              ➊ left          ➋ right; left      ➌ right; right
      -------------------------------------------------------------------
      split_ifs at h with h_l h_r
      -- for ➊: q ∈ inorder l, we use h_l : q < value
      · left
        exact bst_left_ih.mp h -- apply bst_left_ih using only (→) direction
      -- for ➌: q ∈ inorder r, the other way
      · right
        right
        exact bst_right_ih.mp h
      -- for ➋: q = value
      -- since not larger nor smaller then must equal, we close with omega
      · right
        left
        omega
    -- (←) direction
    · intro h
      simp only [inorder, List.mem_append, List.mem_cons] at h
      rw [lookup]
      ----------- CASE SPLIT GOAL -----------------------------------
      split_ifs with h_l h_r
      -- goal 1: lookup q l = true
      · apply bst_left_ih.mpr
        cases h with
        | inl h_inl => trivial -- by hypothesis directly
        | inr h_eq_inr =>
          cases h_eq_inr with
          | inl h_eq => omega
          | inr h_inr => linarith [hright q h_inr]
      -- goal 2: lookup q r = true
      -- similar to goal 1 but just swap positions
      · apply bst_right_ih.mpr
        cases h with
        | inr h_eq_inr =>
          cases h_eq_inr with
          | inl h_eq => omega
          | inr h_inr => exact h_inr
        | inl h_inl => linarith [hleft q h_inl]
      -- goal 3: already true
      · rfl


/-!
  **Exercise 3**

  Prove the following two helper lemmas about `Sorted`.
-/
inductive Sorted : List ℕ → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a : ℕ) (t : List ℕ) : a.MinOfList t → Sorted (t) →  Sorted (a :: t)

-- **(a)** Prove the following lemma.
lemma sorted_a_b (a b : ℕ) (l : List ℕ) (h : Sorted (a :: b :: l)) : a ≤ b := by
  -- we need to split `h : Sorted (a :: b :: l)`
  cases h <;> expose_names
  -- case 1: just trivial
  · exact h
  -- case 2: we found the above by using `simp_all?` directly
  · simp_all only [Nat.MinOfList, List.mem_cons, forall_eq_or_imp]

-- **(b)** Prove the following lemma.
lemma sorted_append (x : ℕ) (l1 l2 : List ℕ) (h1 : Sorted l1) (h2 : Sorted l2)
  (h1' : x.MaxOfList l1) (h2' : x.MinOfList l2) : Sorted (l1 ++ x :: l2) := by
    -- **MyNote:** note that `x :: l2` is sorted because of
    -- `h2' : x.MinOfList l2`
    -- *here, instead of nested `exact Sorted.cons_min x l2 h2' h2`*
    -- *I find the following notion of using `apply` to the constructor easier*
    have h_x_l2 : Sorted (x :: l2) := by
      apply Sorted.cons_min
      · exact h2'
      · exact h2
    -- Then induction on h1 to check all `l1 ++ x :: l2` shall be sorted
    induction h1 with
    -- **case 1:** `l1 = []`
    --    [] ++ x :: l2
    --  = x :: l2
    | nil =>
      rw [List.nil_append] -- [] as neutral element when appending
      exact h_x_l2
    -- **case 2:** `l1 = [a]`
    --   [a] ++ (x :: l2)
    -- =  a :: (x :: l2),  with  a ≤ x
    | single a =>
      simp_all only [Nat.MaxOfList, Nat.MinOfList]
      -- recall:
      apply Sorted.cons
      · apply h1'
        rw [List.mem_singleton]
      · exact h_x_l2
    -- **case 3:** `l1 = a :: b :: t`,  with  a ≤ b  and  Sorted (b :: t)
    --   (a :: b :: t) ++ (x :: l2)
    -- = a :: b :: (t ++ (x :: l2))
    | cons =>
      expose_names
      -- recall: to construct cons, we need
      -- | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
      -- here t is (t ++ (x :: l2))
      apply Sorted.cons
      -- for a ≤ b
      · exact h
      -- for Sorted (b :: t.append (x :: l2))
      · apply a_ih -- since fulfilling a_ih implies our goal, we just show its assumption holds
        -- here if explicit we need to use h1' : x.MaxOfList (a :: b :: t) to conclude
        -- then x is also max of b :: t
        -- but simp_all seems to do the job for us.
        simp_all
    -- **case 4:** `l1 = a :: t`,  with  `h : a.MinOfList t`  and  `h_1 : Sorted t`
    -- earlier we also had `h_x_l2 : Sorted (x :: l2)`
    --   (a :: t) ++ (x :: l2)
    -- = a :: (t ++ (x :: l2))
    | cons_min =>
      expose_names
      -- goal 4.1: show (t ++ (x :: l2)) is sorted
      have h_helper : Sorted (t ++ (x :: l2)) := by
        apply a_ih
        simp_all
      cases t with
      | nil =>
        -- simp_all?
        simp_all only [Nat.MinOfList, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          Nat.MaxOfList, ge_iff_le, List.nil_append, List.mem_cons, or_false, forall_eq,
          List.cons_append]
        apply Sorted.cons
        · exact h1'
        · exact h_x_l2
      | cons =>
        expose_names
        apply Sorted.cons
        · rw [Nat.MinOfList] at h
          apply h
          -- now only need to show head ∈ head :: tail
          -- simp?
          simp only [List.mem_cons, true_or]
        · apply a_ih
          simp_all

/-!
  **Exercise 4**

  For subtask (a), prove that the in-order traversal list of a BST is sorted.
  For subtask (b), construct a binary tree with sorted in-order traversal list
  that is not a BST (according to our definitions).

  You are allowed to use the lemmas from Exercise 3 even if you have not proven
  them.
-/
-- **(a)** Prove the following theorem.
theorem bst_has_sorted_inorder {t : BinaryTree} (ht : IsBST t) : Sorted (inorder t) := by
  induction t with
  | nil => apply Sorted.nil
  | node =>
    expose_names
    -- now check different cases how IsBST holds
    cases ht with
    | node =>
      expose_names
      -- now we can use lemma we just proved
      apply sorted_append
      -- goal 1, 2: Sorted (inorder left), Sorted (inorder right)
      -- directly by inductive hypothesis
      · exact left_ih bst_left
      · exact right_ih bst_right
      -- goal 3: value.MaxOfList (inorder left)
      · have h_helper : Sorted (inorder left):= left_ih bst_left
        -- simp_all?
        simp_all only [imp_self, forall_const, Nat.MaxOfList, ge_iff_le]
        -- introduce y ∈ inorder left
        intro y hy
        -- next we use `hleft : ∀ x ∈ inorder left, x < value` to y, hy
        -- and get `h_helper2 : y < value`
        have h_helper2 := hleft y hy
        omega
      -- goal 4: value.MinOfList (inorder right)
      -- this is just repeating the above but symmetrically
      · have h_helper : Sorted (inorder left):= left_ih bst_left
        -- simp_all?
        simp_all only [imp_self, forall_const, Nat.MinOfList]
        intro y hy
        have h_helper2 := hright y hy
        omega

-- **(b)** Prove the following theorem.
lemma sorted_may_not_imply_bst : ∃ t : BinaryTree, Sorted (inorder t) ∧ ¬ IsBST t := by
  sorry


/-!
  **Exercise 5**

  Prove the theorems (a), (b), (c), and (d) about heaps.
-/

inductive IsHeap : BinaryTree → Prop where
  | nil : IsHeap .nil
  | node (value : ℕ) (l : BinaryTree) (r : BinaryTree)
      (heap_left : IsHeap l) (heap_right : IsHeap r)
      (hleft : ∀ x ∈ inorder l, x ≤ value)
      (hright : ∀ x ∈ inorder r, x ≤ value) :
      IsHeap (.node value l r)

def heapInsert (x : ℕ) : BinaryTree → BinaryTree
  | .nil => .node x .nil .nil
  | .node value l r =>
      if x ≤ value then .node value (heapInsert x r) l
      else .node x (heapInsert value r) l

def fromList : List ℕ → BinaryTree
  | [] => .nil
  | x :: xs => heapInsert x (fromList xs)

-- **(a)** Prove the following theorem.
lemma mem_heapInsert (y : ℕ) (t : BinaryTree) :
    ∀ x : ℕ, y ∈ inorder (heapInsert x t) ↔ y = x ∨ y ∈ inorder t := by
  sorry

-- **(b)** Prove the following theorem.
theorem heapInsert_isHeap {t : BinaryTree} (ht : IsHeap t) :
    ∀ x : ℕ, IsHeap (heapInsert x t) := by
  sorry

-- **(c)** Prove the following theorem.
theorem fromList_isHeap (xs : List ℕ) : IsHeap (fromList xs) := by
  sorry

-- **(d)** Prove the following theorem.
theorem mem_fromList (y : ℕ) (xs : List ℕ) : y ∈ inorder (fromList xs) ↔ y ∈ xs := by
  sorry

end HW5
