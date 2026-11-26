import Mathlib

import waterfall

set_option autoImplicit false

/-!
# Homework 10: one simple algorithm, multiple set implementations

This homework should be less work than the previous ones.

There are four exercises, each worth 25 points.


## Running-time model

Here, we describe running time using separate cost functions that count abstract
operations. This keeps the algorithms simple, but Lean does not ensure that the
cost function follows the algorithm. In the monad-based model, the algorithm and
its cost are defined together. In both cases, Lean cannot ensure that the assigned
costs really represent the intended notion of running time.

For the project, you should use monad-based running-time models. The main point
of this homework is using typeclasses to define and implement interfaces, rather
than running-time modeling.
-/

namespace HW10

/-! ## Exercise 1: an abstract membership interface -/

/-- `Membership α S` says that values of type `S` represent finite sets of
elements of type `α`. -/
class Membership (α : Type) (S : Type) [DecidableEq α] where
  contains : α → S → Bool
  -- Ghost state: not used for the program, but for correctness proofs
  elements : S → Finset α
  contains_correct : ∀ x s, contains x s = true ↔ x ∈ elements s

/-- Count the queries that belong to the represented set. -/
def countHits {α S : Type} [DecidableEq α] [Membership α S]
    (s : S) : List α → Nat
  | [] => 0
  | x :: xs =>
      (if Membership.contains x s then 1 else 0) + countHits s xs

/-!
**Task 1(a).**

Prove correctness using `Membership.contains_correct`.
-/
theorem countHits_correct {α S : Type} [DecidableEq α] [Membership α S]
    (s : S) (queries : List α) : countHits s queries =
      (queries.filter fun x => x ∈ (Membership.elements s : Finset α)).length := by
  induction queries
  · rfl
  · expose_names
    waterfall

/-! Cost model: If `cost x` is the cost of querying `x`, then
`totalLookupCost cost queries` is the cost of all queries. -/
def totalLookupCost {α : Type} (cost : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => cost x + totalLookupCost cost xs

/-!
**Task 1(b).**

Prove that `q` lookups cost at most `q * C` if every lookup costs at most `C`.
-/
theorem totalLookupCost_le {α : Type}
    (cost : α → Nat) (queries : List α) (C : Nat) (hcost : ∀ x, cost x ≤ C) :
    totalLookupCost cost queries ≤ queries.length * C := by
  fun_induction totalLookupCost with
  | case1 =>
    simp
  | case2 elem l ih=>
    grw [ih] -- use inductive hypothesis for inequality
    simp [List.length]
    grind

/-! ## Exercise 2: a list-based set -/

namespace ListSet

variable {α : Type} [DecidableEq α]

/-- Linear search through a list. -/
def contains (x : α) : List α → Bool
  | [] => false
  | y :: ys => if x = y then true else contains x ys

/-- Number of list cells inspected -/
def containsCost (x : α) : List α → Nat
  | [] => 0
  | y :: ys => if x = y then 1 else 1 + containsCost x ys

/-!
**Task 2(a).** Complete the typeclass instance.
-/
instance listMembership : Membership α (List α) where
  contains := contains
  elements := List.toFinset
  contains_correct := by
    expose_names
    intro s l
    induction l
    · -- simp?
      simp only [List.toFinset_nil, Finset.notMem_empty, iff_false, Bool.not_eq_true]
      by_contra
      apply this
      contradiction
    · expose_names
      waterfall


/-!
**Task 2(b).** Prove that one lookup inspects at most `length` cells.
-/
theorem containsCost_le (x : α) (xs : List α) :
    containsCost x xs ≤ xs.length := by
  induction xs
  · rfl
  · expose_names
    -- simp? [containsCost]
    simp only [containsCost, List.length_cons]
    split_ifs <;> expose_names
    · omega
    · omega

/-!
**Task 2(c).** Combine Task 1(b) with Task 2(b).

Thus, if the represented set has `l` list cells and there are `q` queries,
the total lookup cost is at most `q * l`.
-/
theorem totalCost_le (s queries : List α) :
    totalLookupCost (fun x => containsCost x s) queries ≤
      queries.length * s.length := by
  expose_names
  apply totalLookupCost_le -- what we just proved above
  intro h
  apply containsCost_le

/-!
**Instruction:** Prove correctness using one function call in term mode or one `exact` expression.
-/
example (s queries : List Nat) :
    countHits s queries = (queries.filter fun x => x ∈ s.toFinset).length := by
    exact countHits_correct s queries

end ListSet


/-! ## Exercise 3: a tree-based set
-/

inductive BST (α : Type) where
  | nil
  | node (key : α) (left : BST α) (right : BST α)
  deriving Repr

namespace BST

variable {α : Type}

def height : BST α → Nat
  | .nil => 0
  | .node _ left right => 1 + max left.height right.height

def elements [DecidableEq α] : BST α → Finset α
  | .nil => ∅
  | .node key left right => {key} ∪ left.elements ∪ right.elements

/-- Every key in the left subtree is smaller than the root key
and every key in the right subtree is larger. -/
def IsBST [LinearOrder α] : BST α → Prop
  | .nil => True
  | .node key left right =>
      left.IsBST ∧
      right.IsBST ∧
      (∀ x ∈ left.elements, x < key) ∧
      (∀ x ∈ right.elements, key < x)

variable [LinearOrder α]

def contains (x : α) : BST α → Bool
  | .nil => false
  | .node key left right =>
      if x < key then contains x left
      else if key < x then contains x right
      else true

def containsCost (x : α) : BST α → Nat
  | .nil => 0
  | .node key left right =>
      if x < key then 1 + containsCost x left
      else if key < x then 1 + containsCost x right
      else 1

/-! The proof that binary search finds exactly the elements of a IsBST tree is
provided. We need it for the typeclass instance below. -/
theorem contains_correct (x : α) (tree : BST α) (hIsBST : tree.IsBST) :
    contains x tree = true ↔ x ∈ tree.elements := by
  induction tree with
  | nil => simp [contains, elements]
  | node key left right ihLeft ihRight =>
      rcases hIsBST with ⟨hLeft, hRight, hlt, hgt⟩
      by_cases hxk : x < key
      · have hxne : x ≠ key := ne_of_lt hxk
        have hxright : x ∉ right.elements := by
          intro hxmem
          exact lt_asymm hxk (hgt x hxmem)
        simp [contains, elements, hxk, ihLeft hLeft, hxne, hxright]
      · by_cases hkx : key < x
        · have hxne : x ≠ key := (ne_of_lt hkx).symm
          have hxleft : x ∉ left.elements := by
            intro hxmem
            exact lt_asymm (hlt x hxmem) hkx
          simp [contains, elements, hxk, hkx, ihRight hRight, hxne, hxleft]
        · have hxeq : x = key := by
            exact le_antisymm (le_of_not_gt hkx) (le_of_not_gt hxk)
          subst x
          simp [contains, elements]

/-!
**Task 3(a).** Prove that binary search inspects at most `height` nodes.
-/
theorem containsCost_le_height (x : α) (tree : BST α) :
    containsCost x tree ≤ tree.height := by
  induction tree <;> expose_names
  -- case 1: nil
  · rfl
  -- case 2: node
  · waterfall

end BST

/-- A `BSTSet` packages a tree together with its ordering invariant. -/
structure BSTSet (α : Type) [LinearOrder α] where
  tree : BST α
  IsBST : tree.IsBST

namespace BSTSet

variable {α : Type} [LinearOrder α]

/-!
**Task 3(b).** Complete the typeclass instance below using
`BST.contains_correct` and the IsBST proof stored in `s.IsBST`.
-/
instance bstMembership : Membership α (BSTSet α) where
  contains := fun x s => BST.contains x s.tree
  elements := fun s => s.tree.elements
  contains_correct := fun x s => BST.contains_correct x s.tree s.IsBST

def containsCost (x : α) (s : BSTSet α) : Nat :=
  BST.containsCost x s.tree

/-!
**Task 3(c).** Combine Task 1(b) with Task 3(a). A balanced tree would have
logarithmic height, but no balancing theorem is needed here.
-/
theorem totalCost_le (s : BSTSet α) (queries : List α) :
    totalLookupCost (fun x => containsCost x s) queries ≤
      queries.length * s.tree.height := by
  expose_names
  apply totalLookupCost_le
  intro h
  simp only [containsCost]
  apply BST.containsCost_le_height

end BSTSet


/-! ## Exercise 4: combining implementations with lazy evaluation -/

/-! A `UnionSet S T` represents the union of a set represented by `S` and a
set represented by `T`. The two representations may be different:
for example, `S` could be a short list of frequently queried keys
and `T` a larger binary search tree. -/
structure UnionSet (S T : Type) where
  left : S
  right : T

namespace UnionSet

variable {α S T : Type} [DecidableEq α]

/-- Search `left` first and search `right` only after a miss. -/
def contains [Membership α S] [Membership α T]
    (x : α) (s : UnionSet S T) : Bool :=
  Membership.contains x s.left || Membership.contains x s.right

def elements [Membership α S] [Membership α T]
    (s : UnionSet S T) : Finset α :=
  Membership.elements s.left ∪ Membership.elements s.right

/-!
**Task 4(a).** Fill out the `sorry`s and complete the `Membership` instance.
-/

-- helper function
theorem contains_correct [Membership α S] [Membership α T]
    (x : α) (s : UnionSet S T) :
    contains x s = true ↔ x ∈ elements s := by
    simp [contains, elements, Bool.or_eq_true, Finset.mem_union, Membership.contains_correct]

instance unionMembership [Membership α S] [Membership α T] :
    Membership α (UnionSet S T) where
  contains := contains
  elements := elements
  contains_correct := contains_correct

/-! Suppose `leftCost x` and `rightCost x` model the costs of the two
underlying lookups. The left lookup is **always** performed, but the right lookup
is performed **only** if the left lookup returns `false`. -/
def containsCost
    [Membership α S]
    (leftCost rightCost : α → Nat) (x : α) (s : UnionSet S T) : Nat :=
  -- always perform left one
  if Membership.contains x s.left then leftCost x
  else leftCost x + rightCost x

end UnionSet


/-!
**Task 4(b).** Build and test a small two-level set.

1. Define `smallMemory : BSTSet Nat` to contain exactly the keys `2`, `5`, and
   `8`. Use `5` at the root, with `2` as its left child and `8` as its right
   child, and prove that the resulting tree satisfies `BST.IsBST`.

2. Define `smallCache` with the one-element list `[8]` as its fast first set
   and `smallMemory` as its global memory.

3. Replace the `sorry`s in the examples below.
-/

-- helper
-- just an append with a singleton with no other children
def BST.newChild {α : Type} (key : α) : BST α := .node key .nil .nil

-- The small memory
--     5
--    ╱ ╲
--   2   8
def smallMemory : BSTSet Nat where
  tree := .node 5 (.newChild 2) (.newChild 8)
  IsBST := by
    unfold BST.newChild
    simp [BST.IsBST, BST.elements]

-- The small cache has access `left` to a [8]
-- and `right` to the global memory tree
--  ➊ `left`         ➋ `right`
--      [8]               5
--                       ╱ ╲
--                      2   8
def smallCache : UnionSet (List Nat) (BSTSet Nat) where
  left := [8]
  right := smallMemory

def smallCacheCost (x : Nat) : Nat :=
  UnionSet.containsCost
    (fun x => ListSet.containsCost x smallCache.left)
    (fun x => BSTSet.containsCost x smallCache.right)
    x smallCache

example : countHits smallCache [8, 3, 2, 8] = 3 := rfl

example : countHits smallCache [5, 2, 1, 4] = 2 := rfl

example : smallCacheCost 8 = 1 := rfl

example : smallCacheCost 2 = 3 := rfl

end HW10
