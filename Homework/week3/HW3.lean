/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

/-!
# Homework File for Week 3

There are 5 exercises. Each correctly solved exercise is worth 20 points.

You are allowed to use the following tactics:
  `intro`, `ext`, `exact`, `apply`, `cases`, `obtain`, `left`, `right`, `expose_names`,
  `constructor`, `rewrite`, `rw`, `nth_rw`, `have`, `rfl`, `assumption`, `contradiction`,
  `by_contra`, `by_cases`, `unfold`, `use`, `simp`, `simp only`, `grw`, `omega`, `ring`,
  `linarith`, `induction`.

You may also use local definitions using `let`, pattern matching using `match` or `cases`,
and the tactic combinator `<;>`.

As seen in the lecture, it may be helpful to use question-mark tactics such as `simp?`,
`apply?`, `exact?`, and `rw?` while developing your proof. Lean will display a suggested
replacement in the (VS Code) InfoView; you can then replace the question-mark tactic with
that suggestion. The final proof should not contain question-marks.

Definitions introduced in this file are generally not unfolded automatically
by `simp`. When you want to unfold one, name it explicitly; for example,
`simp only [append]`.
-/

/-!
  Exercise 1

  Prove the following theorem by induction over `n` using the `induction` tactic.
-/

def sumPowersOfTwo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumPowersOfTwo n + 2 ^ n

theorem Q1 (n : ℕ) : (sumPowersOfTwo n) + 1 = 2 ^ n := by
  induction n with
  | zero =>
    unfold sumPowersOfTwo -- becomes 0 + 1 = 2 ^ 0
    omega                 -- solve directly
  -- subgoal: sumPowersOfTwo (i + 1) + 1 = 2 ^ (i + 1)
  --                  ↓
  --          sumPowersOfTwo i + 2 ^ i
  --
  -- idea: to change it tothen the `sumPowersOfTwo i` is isolated out,
  -- as it also occurs in induction hypothesis, we can then close the
  -- remaining terms with omega
  | succ i ih =>
    simp only [sumPowersOfTwo]
    omega

/-!
  Exercise 2

  Prove the following theorem by induction over `n` using the `induction` tactic.
  You are allowed to use `Nat.le_induction`.

  Hint: Pattern matching may be useful.
-/
theorem Q2 (n : ℕ) : n ≥ 3 ↔ 2 * n + 2 ≤ 2^n := by
  constructor
  -- subgoal 1: n ≥ 3 → 2 * n + 2 ≤ 2 ^ n
  · intro h
    induction n, h using Nat.le_induction with
    -- subgoal 1.1: to show 2 * 3 + 2 ≤ 2 ^ 3
    | base => trivial
    -- subgoal 1.2: to show 2 * (m + 1) + 2 ≤ 2 ^ (m + 1)
    | succ m hm ih =>
      simp only [mul_add, mul_one] -- make it linear by just simplifying with * rules
      omega                        -- now omega applicable
  -- subgoal 2: 2 * n + 2 ≤ 2 ^ n → n ≥ 3
  · intro h
    -- here we check each case with n = 0,1,2 leading to some impossible
    -- inequalities, then conclude
    match n, h with
    | 0,     h => contradiction
    | 1,     h => contradiction
    | 2,     h => contradiction
    | k + 3, _ => omega

/-
  Consider the following definition of List'
-/
inductive List' (α : Type) where
  | nil : List' α
  | cons (x : α) (xs : List' α) : List' α

namespace List'

def append {α : Type} : List' α → List' α → List' α
  | nil, ys => ys
  | cons x xs, ys => cons x (append xs ys)

def length {α : Type} : List' α → ℕ
  | nil => 0
  | cons _ xs => 1 + length xs

/-!
  Exercise 3

  Prove the following theorems by induction over lists using the `induction` tactic.

  Hint: you only need to use induction over one of the input lists.
-/
theorem Q3a {α : Type} (xs ys zs : List' α) :
    append xs (append ys zs) = append (append xs ys) zs := by
  sorry

theorem Q3b {α : Type} (xs ys : List' α) :
    length (append xs ys) = length xs + length ys := by
  sorry

end List'

/-
  Consider the following definition of BinaryTree'
-/
inductive BinaryTree' (α : Type) where
  | nil
  | node (value : α) (left : BinaryTree' α) (right : BinaryTree' α)

namespace BinaryTree'

/-
  The function `mirror` reflects a binary tree by recursively exchanging
  the left and right subtrees of every node.

  For example, mirroring

          1                                  1
         / \                                / \
        2   3            produces          3   2
           / \                            / \
          4   5                          5   4
-/
def mirror {α : Type} : BinaryTree' α → BinaryTree' α
  | .nil => .nil
  | .node val left right =>
      .node val (mirror right) (mirror left)

/-
  The function `zipWith f` combines two binary trees node by node using `f`.
  Only nodes occurring at the same position in both trees are combined. If
  either tree is `nil` at some position, the result is also `nil` there.

  For example, using addition over natural numbers to combine

          1                  10                            11
         / \                /  \                          /  \
        2   3     and      20  30         produces       22  33
           / \            /      \                             \
          4   5         40       50                            55
-/
def zipWith {α β γ : Type} (f : α → β → γ) :
    BinaryTree' α → BinaryTree' β → BinaryTree' γ
  | .node x left1 right1, .node y left2 right2 =>
    -- Both trees consist of a node => combine with f and recurse
    .node (f x y)
      (zipWith f left1 left2)
      (zipWith f right1 right2)
  | _, _ =>
    -- At least one of the trees is nil => return nil
    .nil

/-!
  Exercise 4

  Prove the following theorem using the `induction` tactic.

  Hint: Perform induction over `t1` before introducing `t2`.
-/
theorem Q4 {α β γ : Type} (f : α → β → γ) (t1 : BinaryTree' α) :
    ∀ t2 : BinaryTree' β,
      mirror (zipWith f t1 t2) =
        zipWith f (mirror t1) (mirror t2) := by
  sorry

end BinaryTree'

namespace RegEx

/-
Exercise 5

A (simplified) regular expression over symbols of type `α` is one of the following:
- **epsilon**: ε, which matches the empty word ""
- **symbol**:  a single symbol of type `α`, e.g. 'a' (when the symbols are characters)
- **choice**:  choice between two regular expressions, e.g. 'a' | ε
- **concat**:  concatenation of two regular expression, e.g. concatenating 'a' and "bc*" gives "abc*"
- **star**:    the repetition of a regular expression *zero or more* times, e.g. "a*", which matches
               "", "a", "aa", "aaa", ...

Task (1) Complete the definition of the inductive type RegEx.
         Use the names marked in **bold** above for the constructors.

Task (2) Complete the definition of the function acceptsEmptyWord.
         It should return `true` if the input regular expression
         matches the empty word "" and `false` otherwise.

         We encourage you to write some testcases using #eval to
         check your implementation.
-/

inductive RegEx (α : Type) where -- Task (1)

def acceptsEmptyWord {α : Type} : RegEx α → Bool := sorry -- Task (2)

end RegEx
