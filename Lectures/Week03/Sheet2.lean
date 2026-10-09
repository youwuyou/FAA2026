/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false

/-! ## Inductive Types

An inductive type is defined by specifying its **constructors**. The constructors
describe all possible ways to create values of the new type.

A constructor may:
* take no arguments, such as `Color.Red`
* take arguments of another type, such as `Option.some 5`
* take arguments of the type currently being defined. Such a constructor is
  called *recursive* and can be used to build structures such as lists and
  binary trees.

Every value of an inductive type is obtained by applying one of its constructors
a finite number of times.
-/

-- # Inductive type: Color 🟥🟩🟦
inductive Color
| Red : Color
| Green : Color
| Blue : Color

#check Color
#check Color.Red

-- Lean can infer the type of the constructor
inductive Color'
| Red
| Green
| Blue

def favoriteColor : Color → String
| Color.Red   => "Red is lovely"
| Color.Green => "Green is calming."
| Color.Blue  => "Blue is clear."

#eval favoriteColor Color.Red

def favoriteColor2 (c : Color) : String :=
  match c with
  | .Red   => "Red is lovely"
  | .Green => "Green is calming."
  | .Blue  => "Blue is clear."


-- # Inductive type: Atomic element and a function
inductive OptionNat
| none : OptionNat
| some : ℕ → OptionNat

#check OptionNat
#check OptionNat.none
#check OptionNat.some
#check OptionNat.some 100

-- We can also define a new type called `MyOption` parameterized by a type α.
-- **MyNote:** so what confused me is not realizing how the 2nd argument works..
-- Also, every constructor always end in `TypeName val1 ... valn`

-- Example 1: here a recursive type, think of ℕ
-- e.g. zero → succ zero → succ (succ zero) → ...
inductive MyNat: Type where
  | zero : MyNat
  | succ: MyNat → MyNat

-- Example 1.1: optional return of nature number
-- think we might need it for a container's return type
inductive OptionMyNat: Type where
  | none: OptionMyNat
  | some: MyNat → OptionMyNat

-- Example 2: optional return of a particular type T
inductive OptionMy_ (T : Type)
| none : OptionMy_ T
| some : T → OptionMy_ T

def orZero : OptionMy_ Nat → Nat
| OptionMy_.none   => 0
| OptionMy_.some n => n

-- mission impossible, if without type T constraint "Inhanbited", we cannot provide
-- such a "default"
def orZero4 (T : Type) [Inhabited T] : OptionMy_ T → T
| OptionMy_.none   => (default : T)    --- it is also ok to just write `default`
| OptionMy_.some n => n

-- pitfalls
def orZeroPitfall : Empty → OptionMy_ Empty → Empty
| zero, OptionMy_.none   => zero -- this case is assuming a contradiction
| _,    OptionMy_.some n => n     -- this too

-- we can now define
def orZero2 (T : Type) : T → OptionMy_ T → T
| zero, OptionMy_.none   => zero
| _,    OptionMy_.some n => n

def safeDiv (T : Type) [Div T] [Inhabited T] [DecidableEq T] (a b : T) : OptionMy_ T :=
  if b = default then OptionMy_.none else OptionMy_.some (a/b)

#eval (10 : Nat) / 0    -- OptionMy_.some 5

-- nevertheless, the class uses this naming...
inductive MyOption (α : Type)| none : MyOption α
| some : α → MyOption α

#check MyOption.some 50
#check MyOption.some "mystring"

-- Alternatively, some : α → MyOption α  can be written as some (a : α)
-- inductive OptionMyNat: Type where
inductive MyOption' (α : Type)
| none
| some (a : α)


-- **Exercise 6**
-- Return the option's element if it has one and the default otherwise
def getOrElse {α : Type} (option : MyOption α) (default : α) : α :=
  match option with
  | MyOption.none => default
  | MyOption.some x => x

-- # Recursive Inductive Type: Nat
-- **MyNote:** I moved the definition above
-- inductive MyNat
-- | zero
-- | succ (n : MyNat)
-- terms of type MyNat: zero, succ zero, succ (succ zero) ...

#check MyNat.zero
#check MyNat.succ (.zero)
#check MyNat.succ (.succ (.zero))
#check MyNat.zero.succ.succ

#check Nat.zero
#check Nat.succ (Nat.zero)

-- Equivalently, we can write it with explicit constructor types
inductive MyNat2
| zero : MyNat2
| succ : MyNat2 → MyNat2


-- # Recursive Inductive Type: List
namespace MyList

-- We define a type `MyList.List` in the namespace here analogous
-- to the built-in type `List` to illustrate how it works
inductive List (α : Type)
| nil
| cons (a : α) (l : List α ) -- a: head (first element), l: tail (rest)
-- A term of type `List α` is either
-- 1. an empty list (`nil`) or
-- 2. `cons head tail` where `head : α` (first element) and `tail` (rest)
-- terms of type List α: nil, cons x nil, cons x (cons y nil), ...

#check List ℕ
#check (List.nil : List ℕ) -- []
#check (List.cons 1 .nil) -- [1]
#check (List.cons 2 (.cons 1 (.nil))) -- [2, 1]

-- Equivalently, it can be written this way using arrow notation
inductive ListF (α : Type)
| nil : ListF α
| cons : α → ListF α → ListF α

#check List
#check List.nil
#check List.cons

-- Example: compute the length of a list
def len {α : Type} : List α → ℕ
| .nil => 0
| .cons x xs => 1 + len xs

-- Example: append a list l2 to a list l1
def append {α : Type} (l1 : List α) (l2 : List α) : List α :=
  match l1 with
  | .nil => l2
  | .cons head l1_rest => .cons head (append l1_rest l2)

-- Example: get i-th element (with MyOption.some) or MyOption.none if out of bounds
def get {α : Type} (l : List α) (i : ℕ) : MyOption α :=
  match l, i with
  | .nil,          _     => MyOption.none
  | .cons head _,  0     => MyOption.some head
  | .cons _ rest,  n + 1 => get rest n

-- My C++ pseudo-code
-- (forward_list = cons-list; recurse on both the list and the index):
-- template <typename T>
-- MyOption<T> get(std::forward_list<T> l, int i){
--   if (l.empty())  return MyOption<T>::none();           // .nil           => none
--   else if (i == 0) return MyOption<T>::some(l.front()); // .cons head _, 0 => some head
--   else {                                                // .cons _ rest, n+1
--     l.pop_front();                                       //   rest
--     return get(l, i - 1);                                //   get rest n
--   }
-- }

-- Example: get i-th element (with MyOption.some) or MyOption.none if out of bounds
def get_master {α : Type} (l : List α) (i : ℕ) : MyOption α :=
  match l with
  | .nil => .none
  | .cons head tail =>
    match i with
    | 0 => .some head
    | j+1 => get tail j

-- **Exercise 7**
-- Define a binary tree as follows:
-- * a **nil** leaf without value or
-- * a **node** with a value of type α and two subtrees left and right
inductive BinaryTree (α : Type)
| nil : BinaryTree α
| node (value : α) (left : BinaryTree α) (right : BinaryTree α) : BinaryTree α

-- Count the number of (non-nil) nodes of a binary tree
def num_nodes {α : Type} : BinaryTree α → ℕ
| BinaryTree.nil => 0                    -- if empty tree, returns zero
| BinaryTree.node _ l_tree r_tree => 1 + num_nodes l_tree + num_nodes r_tree  -- this node + both subtrees

-- My C++ pseudo-code
-- template <T>
-- int num_nodes (std::vector <T>* btree){
--   if (*btree.empty()) return 0;
--   else {
--     return num_nodes(btree->left) + num_nodes(btree->right);
--   }
-- }

end MyList
