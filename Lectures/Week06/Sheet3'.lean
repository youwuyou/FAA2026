/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- Interlude --
-- `structure` in Lean
-- Another way to create a new type is by structure

structure Point where
  x : Nat
  y : Nat

#check Point
-- Point is the type; p is a value of that type.
def p : Point := { x := 3, y := 4 }

#eval p.x
#eval p.y

-- In Lean, a field can contain a proof
structure SortedArrayFun (n : ℕ) where
  get : ℕ → ℕ
  size : ℕ := n -- assigned value
  sorted : Monotone get  -- ∀ ⦃i j : ℕ⦄, i ≤ j → get i ≤ get j

#check SortedArrayFun
#check SortedArrayFun.get
#check SortedArrayFun.sorted
-- A function f is monotone if a ≤ b implies f a ≤ f b.
#check Monotone

-- This is the same as bundling assumptions about this object
-- to create this object, you need to prove these properties.

def exampleArray : SortedArrayFun 5 where
  get := fun i => 2*i
  sorted := by simp [Monotone]

def exampleArray2 : SortedArrayFun 5 := {
  get := fun i => 2*i
  sorted := by simp [Monotone]
}

-- In the proof, we can can obtain these assumption of this type directly
example (n : ℕ) (a : SortedArrayFun n)
    (i j : ℕ) (hij : i ≤ j) :
    a.get i ≤ a.get j := by
    have: Monotone a.get := by exact a.sorted
    simp [Monotone] at this
    simp_all
