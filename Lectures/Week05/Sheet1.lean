/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false

--# Inductive Predicate
-- Today, we cover the concept of an inductive predicate.
-- An inductive predicate is a family of propositions defined by rules
-- for constructing their proofs.
-- Let's start with a toy example.

/- Even number:
  An even number is defined recursively as follows:
  * 0 is even
  * ∀ n : ℕ, if n is even then n + 2 is even
-/

-- General syntax looks like this:
-- | ruleName (inputs...) (proofsOfPremises...) : conclusion

inductive IsEven : ℕ → Prop where
| zero : IsEven 0
| plus_two (n:ℕ): IsEven n → IsEven (n+2)

-- Each constructor is an introduction rule:
-- its arguments are the inputs and premises, and its result is the conclusion.
-- We build proofs of `IsEven` by applying these rules.

-- This gives two (introduction) rules for building a proof that a number is even
#check IsEven.zero
#check IsEven.plus_two

example : IsEven 0 := by
  exact .zero

example : IsEven 4 := by
  apply IsEven.plus_two
  apply IsEven.plus_two
  exact .zero
-- Exercise: Give a forward proof of this

/-!  New Tactics for inductive predicate
  -- `cases h` splits the proof according to which constructor could have produced `h : IsEven n`
  -- In each possible case, Lean introduces that constructor's
  -- arguments and premises, and specializes n and the goal accordingly.
  -- We then prove the goal in each branch.
-/

-- We have seen a speical case of this when we deal with disjunctive predicates
inductive Or' (P Q : Prop) : Prop where
  | left  (hp : P) : Or' P Q
  | right (hq : Q) : Or' P Q


example (P Q : Prop) (h : Or' P Q) : Or' Q P := by
  sorry

example (P Q : Prop) (h : Or' P Q) : Or' Q P := by
  cases h
  · apply Or'.right
    exact hp
  · apply Or'.left
    exact hq

-- case with
example (P Q : Prop) (h : Or' P Q) : Or' Q P := by
  cases h with
  | left =>
    apply Or'.right
    exact hp
  | right =>
    apply Or'.left
    exact hq

-- Define conjunction
inductive And' (P Q : Prop) : Prop
  | intro (hp hq : P) : And' P Q

#check And'.intro

-- Construct a proof by supplying both premises.
example (P Q : Prop) (hp : P) (hq : Q) : And' P Q := sorry

-- Deconstruct a proof to recover both premises.
example (P Q : Prop) (h : And' P Q) : P := sorry

-- Let's prove that 3 is not an even number.
example : ¬ (IsEven 3) := by
  by_contra!
  cases this
  rw [show 0 + 1 = 1 from rfl] at a
  cases a

-- Let's prove completeness and soundness.

-- `cases h` lets us reason about which constructor produced `h : IsEven n`.
-- It works for both concrete numbers and a variable n, but does not
-- provide an induction hypothesis.

-- To prove `P n` for every `n` satisfying `IsEven n`, we can use rule induction.
-- Given `h : IsEven n` and the goal `⊢ P n`, we invoke `induction h`.

-- This produces two cases, corresponding to the constructors of IsEven:
-- • zero: prove P 0.
-- • plus_two: given k, hk : IsEven k, and the induction hypothesis
--   ih : P k, prove P (k + 2).

-- This is called `rule induction` because we induct on the derivation
-- of h, following the rules used to construct a proof of IsEven n.

-- In my view, it is like `cases` tactic, but it gives you inductive hypothesis for free.

@[simp] def evenFun (n : ℕ) : Prop := ∃ k, n = 2*k

theorem soundness_isEven (n : ℕ) (h : IsEven n) :  evenFun n := by
  induction h with
  | zero => simp
  | plus_two n hn ih  =>
    rw [evenFun] at ih
    obtain ⟨k,hk⟩ := ih
    rw [evenFun]
    use k+1
    rw [hk]
    ring

/- # Explanation -/
-- We can think of `h: IsEven n ⊢ P n` as case analysis.
-- Let's consider all rules from inductive predicate `IsEven` that can generate this proof `h: IsEven n`
-- case `IsEven.zero`.     In this case, `h: IsEven n`     is generated from `IsEven 0`, so prove `P 0`
-- case `IsEven.plus_two`. In this case, `h: IsEven (n+2)` is generated from `IsEven n`,
--                         we have `P (n)` and prove `P (n+2)`

inductive IsEven2 : ℕ → Prop
| zero : IsEven2 0
| plus_two (n:ℕ): IsEven2 n → IsEven2 (n+4)

-- Exercise 1.1
theorem soundness_IsEven2 (n : ℕ) : IsEven2 n → evenFun n := sorry

-- Do it together
theorem completeness_isEven (n : ℕ) (h: evenFun n) : IsEven n := by
  rw [evenFun] at h
  obtain ⟨k, hk⟩ := h
  subst hk
  induction k with
  | zero =>
    simp only [mul_zero]
    exact IsEven.zero
  | succ n ih =>
    rw [Nat.mul_add_one 2 n]
    exact IsEven.plus_two (2 * n) ih

-- Exercise 1.2
theorem incompleteness_isEven2 : ∃ n, evenFun n ∧ ¬ IsEven2 n := by sorry

/- Summary
-- By analogy, the proof strategy for inductive predicates is similar to that of the disjunction.
-- h: P ∨ Q    -- `cases h` will deconstruct `h` into  two cases `h: P` and `h: Q` to prove the goal separately
-- h: IsEven n -- `cases h` will deconstruct `h` into cases that `h` can be proved by the constructors.
               -- `induction h` is similar to `cases h`, but we obtain inductive hypothesis to prove the inductive cases.

-- ⊢ P ∨ Q     -- apply `inl: P` or apply `inr: Q` --> this simplifies to proving P or proving Q.
-- ⊢ IsEven n  -- apply `IsEven.zero: IsEven 0` or apply `IsEven.plus_two: IsEven n → IsEven (n+2)`.
-/


-- # Technicality for induction proofs in Lean
-- The arguments for inductive predicates evolves throughout the induction.
-- we can apply `induction h` on h: Even n. However, we cannot apply `induction h` on h: `Even (n+1)`
-- because in Lean `n+1` is not a variable.
-- Example:

-- generalize, replace, rwa tactics
example (m : ℕ) (h : IsEven (m + 2)) : IsEven m := by
  -- Lean does not know that m+2 is a variable
  generalize h_eq: (m+2) = k
  replace h: IsEven k := by rwa [← h_eq]
  induction h
  · sorry
  · sorry

-- Exercise 1.4
example (m n : ℕ) (h: m = 2*n+1) : ¬ IsEven m := by sorry


-- Rule induction produces one case for each constructor.
-- Each case introduces the constructor's arguments and premises.
-- For each recursive premise, it also provides an induction hypothesis.
-- A constructor with no recursive premises gives no induction hypotheses;
-- a constructor with two recursive premises gives two.
-- We must prove the goal in every constructor case.

inductive IsEven' : Nat → Prop where
  | zero : IsEven' 0
  | plus_two (k : Nat) (hk : IsEven' k) : IsEven' (k + 2)
  | add (a b : Nat) (ha : IsEven' a) (hb : IsEven' b) : IsEven' (a + b)

-- Exercise 1.5
example (n : ℕ) (h : IsEven' n) :  evenFun n := by sorry
