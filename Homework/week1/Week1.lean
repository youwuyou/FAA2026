/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# Homework File for Week 1

There are 5 exercises. Each correctly solved exercise is worth 20 points.
-/

section Logic

variable (P Q R S : Prop)

/--
Exercise 1:

Prove the following proposition in **term**-mode.
-/
theorem Q1 (p : P) (q : Q) (pr : P → R) (qrs : Q ∧ R → S) : S :=
  -- You are not allowed to use tactics (`by` keyword) in this task
  sorry

/--
Exercise 2:

Prove the following proposition.
You may only use the tactics `constructor`, `intro`, `apply`, and `exact`.
-/
theorem Q2 : (P → Q ∧ R) ↔ ((P → Q) ∧ (P → R)) := by
  sorry

/--
Exercise 3:

Prove the following proposition. You may only use the tactics
`constructor`, `intro`, `apply`, `exact`, `by_contra`, `contradiction`, and `trivial`.
You may also introduce local definitions using `let`.
-/
theorem Q3 : ((P → Q) ∧ (P → ¬ Q)) ↔ ¬ P := by
  sorry

end Logic

section Divisibility

/-
Consider the following recursive definition of the factorial function:
-/
def fac (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * fac n

/-
In the following exercises, you are *allowed* to use the following theorems:
-/
#check mul_assoc
#check mul_comm
#check dvd_mul_right
#check dvd_trans

/--
Exercise 4:

Show that any positive natural number `n + 1` divides its factorial.
You may only use the tactics `rw`, `rewrite`, `apply`, and `exact`.
-/

theorem Q4 (n : ℕ) : (n + 1) ∣ fac (n + 1) := by
  sorry

/--
Exercise 5:

Show that any divisor `k` of `n + 1` divides any `d` equal to `fac (n + 1)`.
You may only use the tactics `rw`, `rewrite`, `apply`, and `exact`.

Hint: you may want to use the theorem `Q4` that you have proven above.
You will still get the points for this exercise if you have not proven `Q4`.
-/
theorem Q5 (n k d : ℕ) (h : k ∣ (n + 1)) (h2 : fac (n + 1) = d) : k ∣ d := by
  sorry

end Divisibility
