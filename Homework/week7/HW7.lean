import Mathlib
import Cslib.Algorithms.Lean.TimeM
import waterfall

open Cslib.Algorithms.Lean

set_option autoImplicit false
set_option tactic.hygienic false

/-!
# Homework File for Week 7

There are 4 exercises. Each correctly solved exercise is worth 25 points.

All tactics are welcome, unless mentioned explicitly in the task description.
Many induction proofs can be solved using `waterfall`.

We also reserve the right to subtract points for unreadable code.
Please use the code style used in the lecture. If you deviate from it,
please explain why and what the code does in the comments.
-/

namespace HW7

/-- A three-way comparison: `-1` for less than, `0` for equal, and `1` for greater than. -/
def compareNat (x y : ℕ) : ℤ :=
  if x < y then -1 else if x = y then 0 else 1

@[simp] lemma compareNat_eq_neg_one_iff (x y : ℕ) :
    compareNat x y = -1 ↔ x < y := by
  simp [compareNat]
  omega

@[simp] lemma compareNat_eq_zero_iff (x y : ℕ) :
    compareNat x y = 0 ↔ x = y := by
  simp [compareNat]
  omega

@[simp] lemma compareNat_eq_one_iff (x y : ℕ) :
    compareNat x y = 1 ↔ y < x := by
  simp [compareNat]
  omega

/-!
  **Exercise 1: Lookup in a binary search tree**

  As in HW5, we use a binary tree with natural number values.

  One call to `compareNat` costs one time unit.
-/
inductive BinaryTree where
  | nil
  | node (value : ℕ) (left right : BinaryTree)

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

namespace BinaryTree

def height : BinaryTree → ℕ
  | .nil => 0
  | .node _ l r => 1 + max l.height r.height

end BinaryTree

def bstFindT (q : ℕ) : BinaryTree → TimeM ℕ Bool
  | .nil => return false
  | .node x l r => do
      ✓ let c := compareNat q x
      if c = 0 then return true
      else if c = -1 then bstFindT q l
      else bstFindT q r

/-!
  **Task (a)**: Prove the following two helper lemmas.
-/
lemma mem_inorder_node_of_lt {q x : ℕ} {l r : BinaryTree}
    (ht : IsBST (.node x l r)) (hq : q < x) :
    q ∈ inorder (.node x l r) ↔ q ∈ inorder l := by
  sorry

lemma mem_inorder_node_of_gt {q x : ℕ} {l r : BinaryTree}
    (ht : IsBST (.node x l r)) (hq : x < q) :
    q ∈ inorder (.node x l r) ↔ q ∈ inorder r := by
  sorry

/-!
  **Task (b)**: Prove the following two theorems about
  correctness and running time of `bstFindT`.
-/
theorem bstFindT_correct (q : ℕ) (t : BinaryTree) (ht : IsBST t) :
    (bstFindT q t).ret = true ↔ q ∈ inorder t := by
  sorry

theorem bstFindT_time (q : ℕ) (t : BinaryTree) :
    (bstFindT q t).time ≤ t.height := by
  sorry


/-!
**Exercise 2: Regular expressions and the empty word**
-/

-- Recall our regular expression definition without an empty-language constructor.
inductive RegEx (α : Type) where
  | epsilon : RegEx α
  | symbol (a : α) : RegEx α
  | choice (r1 r2 : RegEx α) : RegEx α
  | concat (r1 r2 : RegEx α) : RegEx α
  | star (r : RegEx α) : RegEx α

def regexSize {α : Type} : RegEx α → ℕ
  | .epsilon => 1
  | .symbol _ => 1
  | .choice p q => 1 + regexSize p + regexSize q
  | .concat p q => 1 + regexSize p + regexSize q
  | .star p => 1 + regexSize p

namespace RegEx

variable {α : Type}

/-- Return whether regular expression accepts the empty word. -/
def matchEpsilon : RegEx α → Bool
  | .epsilon => true
  | .symbol _ => false
  | .choice p q => p.matchEpsilon || q.matchEpsilon
  | .concat p q => p.matchEpsilon && q.matchEpsilon
  | .star _ => true

/-- The acceptance relation for regular expressions. -/
def Matches : RegEx α → List α → Prop
  | .epsilon, w => w = []
  | .symbol a, w => w = [a]
  | .choice p q, w =>
      p.Matches w ∨ q.Matches w
  | .concat p q, w =>
      ∃ u v : List α, w = u ++ v ∧ p.Matches u ∧ q.Matches v
  | .star p, w =>
      ∃ words : List (List α), w = words.flatten ∧ ∀ word ∈ words, p.Matches word

/-- The language denoted by a regular expression. -/
def MatchSet (r : RegEx α) : Set (List α) := { w | r.Matches w }

/-!
  **Task (a)**

  Prove the following lemma.
-/
lemma matchEpsilon_eq_true_iff (r : RegEx α) :
    r.matchEpsilon = true ↔ r.Matches [] := by
  sorry


/-- Timed implementation of `matchEpsilon`. -/
def matchEpsilonT {α : Type} : RegEx α → TimeM ℕ Bool
  | .epsilon => do ✓ return true
  | .symbol _ => do ✓ return false
  | .choice p q => do
      ✓
      let hp ← matchEpsilonT p
      let hq ← matchEpsilonT q
      return hp || hq
  | .concat p q => do
      ✓
      let hp ← matchEpsilonT p
      let hq ← matchEpsilonT q
      return hp && hq
  | .star _ => do ✓ return true


theorem matchEpsilonT_correct {α : Type} (r : RegEx α) :
    (matchEpsilonT r).ret = r.matchEpsilon := by
  waterfall

theorem matchEpsilonT_time {α : Type} (r : RegEx α) :
    (matchEpsilonT r).time ≤ regexSize r := by
  waterfall

/-!
  **Task (b)**

  Prove the following two statements.
  The *second* subtask must be proven using **only** `rw`.
-/
lemma matchEpsilonT_time5 {α : Type} : ∃ r : RegEx α, (matchEpsilonT r).time = 5 := by
  sorry

/--
**Instruction**: Complete this theorem using **only** `rw`.
You should use the theorems proven in this exercise.
Hint: you might find a `Set` lemma from HW2 useful.
-/
theorem matchEpsilonT_semantic {α : Type} (r : RegEx α) :
    (matchEpsilonT r).ret = true ↔ [] ∈ r.MatchSet := by
  sorry

/-!
  **Exercise 3: Lazy evaluation**

  **Task (a)**:

  Implement `matchEpsilonT'` such that it uses *lazy* evaluation.
  Lazy evaluation means that a value is only computed when needed.
  For example, when we want to evaluate an expression `A ∨ B`
  and we have already evaluated `A` to be true, then we do not
  need to evaluate `B`. Eager evaluation, on the other hand,
  evaluates `B` in all cases.

  You can read more about lazy evaluation here:
  https://en.wikipedia.org/wiki/Lazy_evaluation
 -/
def matchEpsilonT' {α : Type} : RegEx α → TimeM ℕ Bool := sorry

theorem matchEpsilonT'_correct {α : Type} (r : RegEx α) :
    (matchEpsilonT' r).ret = r.matchEpsilon := by
  sorry -- use `waterfall`

theorem matchEpsilonT'_cost {α : Type} (r : RegEx α) :
    (matchEpsilonT' r).time ≤ (matchEpsilonT r).time := by
  sorry -- use `waterfall`

/-!
  **Task (b)**

  Prove the following two theorems to show that the
  lazy evaluation implementation is always at least
  as fast as the basic implementation and has linear
  speedup for some inputs.
-/

theorem matchEpsilonT'_linear_speedup (n : ℕ) (b : Bool) :
    ∃ r : RegEx Char,
      regexSize r = 2 * n + 3 ∧
      (r.Matches [] ↔ b) ∧
      (matchEpsilonT r).time = regexSize r ∧
      (matchEpsilonT' r).time = 2 := by
  sorry

end RegEx


/-!
  **Exercise 4: Counting in a (sorted) list**

The baseline program counts how often `q` occurs in an arbitrary list, charging
one time unit per call to `compareNat`. Prove its correctness and exact cost.

Then exploit sortedness: `countSortedT` stops as soon as it finds an element
larger than `q`. Prove that this optimization is correct for sorted lists,
establish its worst-case cost, and exhibit sorted inputs on which it takes
one step while the baseline takes arbitrarily many.
-/

def countT (q : ℕ) : List ℕ → TimeM ℕ ℕ
  | [] => return 0
  | x :: xs => do
      ✓ let c := compareNat x q
      let n ← countT q xs
      return if c = 0 then n + 1 else n

@[simp] theorem countT_correct (q : ℕ) (xs : List ℕ) :
    (countT q xs).ret = xs.count q := by
  waterfall

@[simp] theorem countT_time (q : ℕ) (xs : List ℕ) :
    (countT q xs).time = xs.length := by
  waterfall

@[simp] theorem countT_eq_zero_iff (q : ℕ) (xs : List ℕ) :
    (countT q xs).ret = 0 ↔ q ∉ xs := by
  rw [countT_correct]
  exact List.count_eq_zero

/-!
  **Task (a)**: Implement `countSortedT` such that it returns *as soon as*
  it finds an element larger than `q`.
-/

def countSortedT (q : ℕ) : List ℕ → TimeM ℕ ℕ := sorry

-- Hint: `List.pairwise_cons` might be useful for (b).

/-!
  **Task (b)**: Prove that `countSortedT` is correct for sorted lists.
-/
theorem countSortedT_correct (q : ℕ) (xs : List ℕ) (hs : xs.Pairwise (· ≤ ·)) :
    (countSortedT q xs).ret = xs.count q := by
  sorry

/-!
  **Task (c)**: Prove that the optimized implementation is always at least
  as fast as the baseline and that it has linear speedup for some inputs.
-/
theorem countSortedT_time_le (q : ℕ) (xs : List ℕ) :
    (countSortedT q xs).time ≤ (countT q xs).time := by
  sorry

theorem countSortedT_linear_speedup (n : ℕ) :
    ∃ xs : List ℕ,
      xs.Pairwise (· ≤ ·) ∧
      xs.length = n + 1 ∧
      (countSortedT 0 xs).time = 1 ∧
      (countT 0 xs).time = n + 1 := by
  sorry


end HW7
