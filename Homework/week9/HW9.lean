/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import Mathlib
import Cslib.Algorithms.Lean.TimeM
import waterfall

open Cslib.Algorithms.Lean

set_option autoImplicit false
set_option tactic.hygienic false

/-!
# Homework File for Week 9

There are 2 exercises, each worth 50 points.

All tactics are welcome, unless mentioned explicitly in the task description.
Many induction proofs can be solved using `waterfall`.

We also reserve the right to subtract points for unreadable code.
Please use the code style used in the lecture. If you deviate from it,
please explain why and what the code does in the comments.
-/

namespace HW9

/-!
  **Exercise 1: The Extended Euclidean algorithm**

  The extended Euclidean algorithm computes `g = gcd a b` together with
  *Bézout coefficients* `s` and `t` such that `s * a + t * b = g`.

  It is based on two facts:
  * `gcd a b = gcd b (a % b)` and `gcd a 0 = a`,
  * `a % b = a - (a / b) * b`. Hence, if `s' * b + t' * (a % b) = g`,
    then `t' * a + (s' - (a / b) * t') * b = g`.

  Informal description of the algorithm `gcd(a,b)`:
  * if `b = 0`: return GCD `a` and Bézout coefficients `1`, `0`
  * otherwise:
    * Let `q = a/b` and `r = a%b`, then `a = q*b + r`
    * Call `gcd(b, r)`; let `g` be the returned GCD and `s`, `t` the coefficients.
      Return GCD `g` and coefficients `t`, `s - q*t`
-/

def divStep (a b : ℕ) : ℕ × ℕ := (a / b, a % b)

@[simp] lemma divStep_fst (a b : ℕ) : (divStep a b).1 = a / b := rfl
@[simp] lemma divStep_snd (a b : ℕ) : (divStep a b).2 = a % b := rfl

/-!
  **Task (a)**: Fill out the algorithm definition and prove termination.

  Cost model:
  * one division step (computing `a / b` and `a % b`) costs one time unit;
    you can ignore other operations such as multiplications and subtractions.
  * use the function `divStep` for this and charge one time unit per call
  * If you want something like `let (q,r) := divStep a b`, you should write
    `let qr := divStep a b`;`let q := qr.1`;`let r := qr.2`; Lean seems to
    struggle with the tuple notation inside the monad expression.
-/

-- The following theorem might be useful for the termination proof
#check Nat.mod_lt

/-- Returns `(g, s, t)` with `g = gcd a b` and `s * a + t * b = g`. -/
def xgcdT (a b : ℕ) : TimeM ℕ (ℤ × ℤ × ℤ) :=
  -- we follow the description and took some inspirations from `bfs_rec` sheet3 week09
  if h : b = 0 then
    return (a, 1, 0)
  else do
    -- ➊ compute with helper function divStep
    --  * Let `q = a/b` and `r = a%b`
    ✓
    let qr := divStep a b -- (a / b, a % b)
    let q := qr.1         -- obtain a / b
    let r := qr.2         -- obtain a % b

    -- ➋ * Call `gcd(b, r)`; let `g` be the returned GCD and `s`, `t` the coefficients.
    let ⟨g, s, t⟩ ← xgcdT b r

    -- ➌ Return GCD `g` and coefficients `t`, `s - q*t`
    return (g, t, s - q * t)
termination_by b
-- we have a % bi < bi with decreasing bi
decreasing_by
  exact Nat.mod_lt a (Nat.pos_of_ne_zero h)


/-- `xgcdTest a b result steps` checks the observable behavior of `xgcdT a b`. -/
abbrev xgcdTest (a b : ℕ) (result : ℤ × ℤ × ℤ) (steps : ℕ) : Prop :=
  (xgcdT a b).ret = result ∧ (xgcdT a b).time = steps
/-! You can check your algorithm using the following test cases. -/
-- example : xgcdTest 0 0 (0, 1, 0) 0 := by native_decide
-- example : xgcdTest 17 0 (17, 1, 0) 0 := by native_decide
-- example : xgcdTest 0 17 (17, 0, 1) 1 := by native_decide
-- example : xgcdTest 42 42 (42, 0, 1) 1 := by native_decide
-- example : xgcdTest 21 7 (7, 0, 1) 1 := by native_decide
-- example : xgcdTest 7 21 (7, 1, 0) 2 := by native_decide
-- example : xgcdTest 54 24 (6, 1, -2) 2 := by native_decide
-- example : xgcdTest 13 7 (1, -1, 2) 3 := by native_decide
-- example : xgcdTest 240 46 (2, -9, 47) 5 := by native_decide
-- example : xgcdTest 144 89 (1, 34, -55) 10 := by native_decide

/-!
  **Task (b)**: Prove that `xgcdT` is correct, i.e. it returns the gcd
  and Bézout coefficients for it.

  Hint 1: generalize the output variables `g`, `s`, and `t` in the functional induction.

  Hint 2: If you have a recursive call, it may be useful to name the result of the
  recursive call, e.g. you can name it `(g', s', t')` as follows:
  `rcases h_rec : (xgcdT b (a % b)).ret with ⟨g', s', t'⟩`
-/

-- The following lemma might be useful.
lemma h_div (a b : ℕ) : ((a % b : ℕ) : ℤ) + b * (a / b : ℕ) = a := by
  exact_mod_cast Nat.mod_add_div a b

theorem xgcdT_correct (a b : ℕ) (g s t : ℤ) (h_result : (xgcdT a b).ret = (g, s, t)) :
    g = Nat.gcd a b ∧ s * a + t * b = g := by
    sorry


/-!
  **Task (c)**: Prove that `xgcdT` needs at most `2 * log₂ b + 1` division steps.
  Also fill out the helper lemma `xgcdT_time_step`.

  Hint: `fun_induction` is not enough. Its hypothesis only talks about the *next* call
  `(b, a % b)`, but the second argument is only guaranteed to halve after *two* steps.
  Use strong induction on `b` instead (`induction b using Nat.strong_induction_on`),
  together with the following helper lemmas.
-/

/-- If `0 < r ≤ b`, then `b % r` is strictly less than half of `b`, in the sense that
`2 * (b % r) < b`: either `r ≤ b / 2` and `b % r < r`, or `r > b / 2` and
`b % r = b - r`. -/
@[simp] lemma mod_mul_two_lt {r b : ℕ} (hr : 0 < r) (hrb : r ≤ b) : b % r * 2 < b := by
  have hmod : b % r < r := Nat.mod_lt b hr
  have hdiv : b % r + r * (b / r) = b := Nat.mod_add_div b r
  have hquotient : r ≤ r * (b / r) := Nat.le_mul_of_pos_right r (Nat.div_pos hrb hr)
  omega

/-- Halving decreases the logarithm by one. -/
@[simp] lemma log_add_one_le {m b : ℕ} (hb : 2 ≤ b) (hm : m * 2 < b) :
    Nat.log 2 m + 1 ≤ Nat.log 2 b := by
  apply Nat.le_log_of_pow_le (by norm_num)
  rw [pow_succ]
  by_cases hm0 : m = 0
  · simp [hm0]
    omega
  · have hpow := Nat.pow_log_le_self 2 hm0
    omega

/-- Unfolding one step of `xgcdT`. -/
@[simp] lemma xgcdT_time_step (a b : ℕ) (hb : b ≠ 0) :
    (xgcdT a b).time = (xgcdT b (a % b)).time + 1 := by
  rw [xgcdT]
  -- our hb is b ≠ 0 case in the else case
  simp [hb]
  ring

theorem xgcdT_time (a b : ℕ) : (xgcdT a b).time ≤ 2 * Nat.log 2 b + 1 := by
  sorry


/-!
  **Exercise 2: Depth-first search**

  A directed graph on the vertices `Fin n = {0, ..., n - 1}` is represented by the finite
  set of outgoing neighbors of each vertex. We sort these sets to obtain deterministic
  adjacency lists for a concrete implementation of DFS.

  Depth-first search keeps a stack of vertices that still have to be explored. It pops a
  vertex `v`; if `v` was not visited yet, it visits `v` and pushes all neighbors of `v`.
  Since new vertices are pushed on top, the search always continues from the most recently
  visited vertex. The result is the list of visited vertices, most recently visited first.

  Cost model: one time unit per stack pop.
-/

namespace DFS

variable {n : ℕ}

/-- A finite directed graph, represented by its outgoing neighbors. -/
structure DiGraph (n : ℕ) where
  outNeighbors : Fin n → Finset (Fin n)

/-- There is a directed edge from `u` to `v`. -/
def DiGraph.Adj (G : DiGraph n) (u v : Fin n) : Prop :=
  v ∈ G.outNeighbors u

/-- A deterministic list representation of the outgoing neighbors of `u`.

Unlike `Finset.toList`, sorting gives executable code and fixes the order used by the
example below. The correctness and running-time proofs use only membership and length.
-/
def DiGraph.toList (G : DiGraph n) (u : Fin n) : List (Fin n) :=
  (G.outNeighbors u).sort (· ≤ ·)

@[simp] lemma DiGraph.mem_toList (G : DiGraph n) {u v : Fin n} :
    v ∈ G.toList u ↔ G.Adj u v := by
  simp [toList, Adj]

/-- Depth-first search with one unit of cost per stack pop. -/
def dfsT (G : DiGraph n) :
    List (Fin n) → List (Fin n) → TimeM ℕ (List (Fin n))
  | [], visited =>
    return visited
  | v :: stack, visited => do
    ✓
    if v ∈ visited then
      dfsT G stack visited
    else
      dfsT G (G.toList v ++ stack) (v :: visited)
termination_by
  -- The cardinality of visited increases or the stack length decreases
  stack visited => (n - visited.toFinset.card, stack.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have hv : v ∉ visited.toFinset := by simpa
    have := Finset.card_lt_univ_of_notMem hv
    simp only [List.toFinset_cons, Finset.card_insert_of_notMem hv, Fintype.card_fin] at *
    omega

/- The graph `0 → 1`, `0 → 2`, `1 → 3`, `2 → 3`, `3 → 1`, `4 → 0`. -/
def exampleGraph : DiGraph 5 where
  outNeighbors
    | 0 => {1, 2}
    | 1 => {3}
    | 2 => {3}
    | 3 => {1}
    | 4 => {0}

example : (dfsT exampleGraph [0] []).ret = [2, 3, 1, 0] ∧
    (dfsT exampleGraph [0] []).time = 6 := by
  native_decide

/-- `v` is reachable from the graph vertex `s`. -/
inductive Reach (G : DiGraph n) (s : Fin n) : Fin n → Prop
  | refl : Reach G s s
  | tail {u v : Fin n} : Reach G s u → G.Adj u v → Reach G s v

/-- The number of directed edges, counted by their source. -/
def numEdges (G : DiGraph n) : ℕ :=
  ∑ v, (G.toList v).length

/-!
  **Task (a)**: Prove that DFS from `s` visits every vertex at most once, and that it visits
  exactly the vertices that are reachable from `s`. We supply the proof of the first invariant;
  please fill out the others.
-/

/-- Only reachable vertices are visited. -/
lemma dfsT_reach (G : DiGraph n)
    (s : Fin n) (stack visited : List (Fin n))
    (hstack : ∀ v ∈ stack, Reach G s v) (hvisited : ∀ v ∈ visited, Reach G s v) :
    ∀ v ∈ (dfsT G stack visited).ret, Reach G s v := by
  fun_induction dfsT G stack visited with
  | case1 visited => simpa using hvisited
  | case2 w stack visited ih_skip ih_visit =>
    simp only [TimeM.ret_bind]
    have hw : Reach G s w := hstack w List.mem_cons_self
    split_ifs with hw'
    · exact ih_skip (fun v hv => hstack v (List.mem_cons_of_mem _ hv)) hvisited
    · apply ih_visit hw'
      · intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact Reach.tail hw (G.mem_toList.mp hv)
        · exact hstack v (List.mem_cons_of_mem _ hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hw
        · exact hvisited v hv

/-- No vertex is visited twice. -/
lemma dfsT_nodup (G : DiGraph n)
  (stack visited : List (Fin n))
  (h : visited.Nodup) : (dfsT G stack visited).ret.Nodup := by
  waterfall

/-- Vertices that are visited or on the stack will be visited. -/
lemma mem_dfsT (G : DiGraph n)
    (stack visited : List (Fin n)) (v : Fin n)
    (h : v ∈ visited ∨ v ∈ stack) : v ∈ (dfsT G stack visited).ret := by
  waterfall

/-- When DFS stops, all neighbors of visited vertices are visited. -/
lemma dfsT_closed (G : DiGraph n)
    (stack visited : List (Fin n))
    (h : ∀ u ∈ visited, ∀ w, G.Adj u w → w ∈ visited ∨ w ∈ stack) :
    ∀ u ∈ (dfsT G stack visited).ret, ∀ w, G.Adj u w →
      w ∈ (dfsT G stack visited).ret := by
  -- we try similar as reach proof above
  fun_induction dfsT G stack visited with
  | case1 visited => simpa using h
  | case2 =>
    simp only [TimeM.ret_bind]
    sorry


theorem dfsT_correct (G : DiGraph n) (s v : Fin n) :
    v ∈ (dfsT G [s] []).ret ↔ Reach G s v := by
  sorry

theorem dfsT_visits_once (G : DiGraph n)
    (s : Fin n) :
    (dfsT G [s] []).ret.Nodup := by
  -- above we proved the lemma that no vertices are visited twice
  simp [dfsT_nodup]

/-!
  **Task (b)**: Prove that DFS takes at most one time unit per edge (plus one for `s`).

  This is the promised cost analysis of the concrete list implementation. The bound counts
  each outgoing-neighbor entry once, when its source vertex is first visited.

  Hint: Every vertex is visited at most once, and only then its neighbors are pushed.
  Bound the time of `dfsT` by the length of the stack plus the number of edges leaving
  unvisited vertices.
-/

lemma dfsT_time_le (G : DiGraph n)
    (stack visited : List (Fin n)) :
    (dfsT G stack visited).time ≤
      stack.length + ∑ v ∈ visited.toFinsetᶜ, (G.toList v).length := by
  sorry

theorem dfsT_time (G : DiGraph n) (s : Fin n) :
    (dfsT G [s] []).time ≤ numEdges G + 1 := by
  sorry

end DFS


end HW9
