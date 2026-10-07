/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false

/-!
# Homework File for Week 4

There are 5 exercises. Each correctly solved exercise is worth 20 points.

Unless stated otherwise, you are allowed to use the following tactics:
  `intro`, `ext`, `exact`, `apply`, `assumption`, `rfl`, `constructor`,
  `left`, `right`, `use`, `have`, `obtain`, `cases`, `induction`,
  `fun_induction`, `rename_i`, `expose_names`, `by_cases`, `by_contra`,
  `contradiction`, `unfold`, `rewrite`, `rw`, `nth_rw`, `simp`,
  `simp only`, `grw`, `ring`, `ring_nf`, `norm_num`, `linarith`,
  `nlinarith`, `omega`, `gcongr`, and `split`.

You may also use local definitions with `let`, pattern matching with `match`,
and the tactic combinator `<;>`.
-/


/-!
  **Exercise 1**

  Prove the following theorem using `fun_induction`.
-/
def oddSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => oddSum n + (2 * n + 1)

theorem Q1 (n : ℕ) : oddSum n = n ^ 2 := by
  sorry


/-!
  **Exercise 2**

  The recurrence `halvingWork n` models the running time of an algorithm that
  performs `n` steps and then recursively processes an input of size `n / 2`.
  Note that natural number division rounds down the input.

  Prove the stated linear upper bound using strong induction.
-/

def halvingWork : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + halvingWork ((n + 1) / 2)

#eval List.map halvingWork [0, 1, 2, 3, 4, 8, 16]
-- [0, 1, 3, 4, 7, 15, 31]

theorem Q2 (n : ℕ) : halvingWork n ≤ 2 * n := by
  sorry

/-!
  **Exercise 3**

  Prove both inequalities using a single `calc` block. Each calculation step
  may use at most four tactic invocations, chosen from `rfl`, `exact`, `apply`,
  `assumption`, `rw`, `nth_rw`, `simp`, `simp only`, `ring`, `ring_nf`,
  `norm_num`, `linarith`, `nlinarith`, `omega`, and `gcongr`.

  You may use `simp` with its default simplification lemmas. The only additional
  named results that may be supplied explicitly to a tactic are `sq_nonneg` and
  `Q3a` when proving part (b).

  Hint: You can supply arguments to `linarith`, `nlinarith`, `gcongr` in `[...]`,
  like when using `simp [...]`.
-/
#check sq_nonneg

-- (a)
-- Hint: First think about on paper how to rewrite (a + b) ^ 2 suitably to bring
-- it close to the right-hand side.
theorem Q3a (a b : ℤ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  sorry

-- (b)
theorem Q3b (a b c : ℤ) :
    (a + b + c) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  sorry

/-!
  **Exercise 4**

  Prove the theorem below about tripleZipWith.

  Hint: If `simp` is unable to simplify a pattern matching expression,
  a case distinction might be useful.
-/
def zipWith {α β γ : Type} (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: zipWith f xs ys

def tripleZipWith {α β γ δ : Type} (f : α → β → γ → δ)
  : List α → List β → List γ → List δ
  | [], _, _ => []
  | _, [], _ => []
  | _, _, [] => []
  | x :: xs, y :: ys, z :: zs => f x y z :: tripleZipWith f xs ys zs

theorem Q4 {α β γ δ : Type} (f : α → β → γ → δ)
    (xs : List α) (ys : List β) (zs : List γ) :
    tripleZipWith f xs ys zs = zipWith (fun (g : γ → δ) (y : γ) ↦ g y) (zipWith f xs ys) zs
    := by
    sorry


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

/-
  A tuple type `A × B` (type "\times" or "\x") is a type of tuples `(a, b)` such that `a : A` and `b : B`.

  Consider the following definition of append', which returns a tuple `(zs, t)`.
  * `zs` is a list, and it is the same as `append xs ys`.
  * `t` is a counter that is incremented for every element that is added to `zs`
-/
def aux {α : Type} : List' α → (List' α × ℕ) → (List' α × ℕ)
  | nil, (ys, n) =>
      (ys, n)
  | cons x xs, ysn =>
      let (zs, m) := aux xs ysn
      (cons x zs, m+1)

def append' {α : Type} (xs ys : List' α) : (List' α × ℕ) :=
  aux xs (ys, 0)

def appendE {α : Type} (xs ys : List' α) := (append' xs ys).1
def appendT {α : Type} (xs ys : List' α) := (append' xs ys).2

/-!
  **Exercise 5**

  Prove the following theorems.

  Hint: Since `append'` is defined using `aux`, it is helpful to first prove
  a stronger statement about `aux` and then reuse it in the two main proofs.
-/

theorem Q5a {α : Type} (xs ys : List' α) :
    appendE xs ys = append xs ys := by
  sorry

theorem Q5b {α : Type} (xs ys : List' α) :
    appendT xs ys = length xs := by
  sorry
