/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import Mathlib
import Cslib.Algorithms.Lean.TimeM

open Cslib.Algorithms.Lean

set_option autoImplicit false

/-!
# Homework 8

**Coloring a graph with `Δ(G) + 1` colors in linear time**

A *proper coloring* of a graph gives every vertex a color such that the two endpoints of every
edge get different colors. Every graph with maximum degree `Δ(G)` can be colored with
`Δ(G) + 1` colors, and the *greedy algorithm* finds such a coloring: it goes through the vertices
one after the other and gives each vertex the smallest color that none of its already colored
neighbors has. A vertex has at most `Δ(G)` neighbors, so one of the colors `0, ..., Δ(G)` is
always free. With the right data structures, the greedy algorithm runs in linear time
`O(n + m)`.

## Tasks

* Model the problem: what is a proper coloring, the maximum degree `Δ(G)`, and the size of the
  input?
* Implement the greedy algorithm in `TimeM`. `TimeM` only counts the ticks that you write, so
  choose a cost model that describes what your algorithm would cost on a real computer, and
  explain in a comment for every tick which operations it pays for.
* Test your algorithm on a few graphs.
* (Optional) Prove that your algorithm computes a proper coloring with `Δ(G) + 1` colors.
* (Optional) Prove that your algorithm runs in linear time.

Below is a proposal for how to represent graphs. You may use it, or define your own.
-/

namespace HW8

-- *problem modeling*
-- we additionally added `sorted` to ➊ avoid multi-edges & ➋ de-duplicate

/-- An undirected graph without self-loops on the vertices `Fin n = {0, ..., n - 1}`,
given by its adjacency lists: `v ∈ G.adj u` means that `u` and `v` are adjacent. -/
structure Graph (n : ℕ) where
  /-- The adjacency list of every vertex. -/
  adj : Fin n → List (Fin n)
  /-- Edges are undirected. -/
  symm : ∀ u v, v ∈ adj u → u ∈ adj v
  /-- There are no self-loops. -/
  loopless : ∀ v, v ∉ adj v
  /-- Adjacency lists are strictly sorted. -/
  sorted : ∀ u, (adj u).Pairwise (· < ·)

namespace Graph

variable {n : ℕ}


-- *specifications* what is a proper coloring?
-- A k-coloring is a map from the vertex set to the `Fin k := {0, 1, ..., k-1}`
abbrev Coloring n k := Fin n → Fin k

-- A proper k-coloring requires if `u ∈ adj v => c(u) != c(v)`
-- *MyNote:* added reducible here to make the decide work on properness example check later.
@[reducible] def IsProperColoring {n k : ℕ} (G : Graph n) (c : Coloring n k) : Prop :=
  ∀ v, ∀ u ∈ G.adj v, c u ≠ c v

-- here we use the existence statement in order to tie a concrete coloring to a proposition
def Colorable {n : ℕ} (k : ℕ) (G : Graph n) : Prop :=
  ∃ c : Coloring n k, IsProperColoring G c

-- *derived properties of the graph*
def degree (v : Fin n) (G : Graph n) : ℕ := (G.adj v).length
def maxDegree (G : Graph n) : ℕ := Finset.univ.sup G.degree

-- some helpers. we only used them later for the concrete graph tests
def numVertices (_ : Graph n) : ℕ := n
def numEdges (G : Graph n) : ℕ := ((List.finRange n).map (G.degree ·)).sum / 2

-- *algorithm*
-- ➌ [findFreeT]
def findFreeT {d : ℕ} (used : Vector Bool (d + 1)) : List (Fin (d + 1)) → TimeM ℕ (Fin (d + 1))
  | []      => return 0
  | color :: other_colors => do
    -- we check one entry of boolean vector `used` to see if the bit is set
    ✓ let bit_set := used[color]
    if bit_set then findFreeT used other_colors else return color

-- *main idea:*
-- going through v in vertices of the graph
-- check for each neighbor u ∈ adj v and see what numbers/colors are taken
-- assign the lowest still available number of Fin (d + 1) to v
-- return the assignment
def greedyT (G : Graph n) (d : ℕ) : TimeM ℕ (Vector (Fin (d + 1)) n) := do
  -- construct available color list once
  let palette := List.finRange (d + 1)
  -- tracking result and intermediate states
  let mut colors : Vector (Fin (d + 1)) n := Vector.replicate n 0
  let mut used   : Vector Bool (d + 1)    := Vector.replicate (d + 1) false
  for v in List.finRange n do
    -- ➊ [set]
    for u in G.adj v do
      -- we mark a bit in `used` for possible neighbors
      ✓ if u < v then
          used := used.set colors[u].val true colors[u].isLt
    let color ← findFreeT used palette
    -- ➋ [assign_color]
    ✓ colors := colors.set v.val color v.isLt
    -- ➌ [reset]
    -- we unmark the bit in `used` to prepare for the next vertex to be colored
    for u in G.adj v do
      ✓ if u < v then
          used := used.set colors[u].val false colors[u].isLt
  return colors

-- *correctness (Optional)*
-- [TODO] to show properness formally; sorry I had no time but I tested below! :)

-- *computational cost (Optional)*
-- [TODO] to show the cost is indeed `O(n + m)`; again no time but I tested below too.

/-! ## Example graphs

Test your algorithm on these graphs, and on your own ones.
-/

/-- The graph with the edges `E`: every edge `(u, v)` is stored in the adjacency lists of both
`u` and `v`. For a concrete list `E`, Lean checks automatically that it has no self-loops.

For example, `Graph.ofEdges [(0, 1), (1, 2)] : Graph 3` is the path `0 - 1 - 2`. -/
def ofEdges (E : List (Fin n × Fin n)) (hE : ∀ e ∈ E, e.1 ≠ e.2 := by decide) : Graph n where
  -- ensure the adjacency list is strictly sorted by filtering
  adj v := (List.finRange n).filter (fun u => decide ((u, v) ∈ E ∨ (v, u) ∈ E))
  symm u v h := by
    grind
  loopless v h := by
    grind
  sorted u := (List.pairwise_lt_finRange n).filter _

/-- The graph without vertices. -/
def G1 : Graph 0 := .ofEdges []

/-- The path `0 - 1 - 2 - 3`. -/
def G2 : Graph 4 := .ofEdges [(0, 1), (1, 2), (2, 3)]

/-- The complete graph `K₄`. -/
def G3 : Graph 4 := .ofEdges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The odd cycle `0 - 1 - 2 - 3 - 4 - 0`, which needs 3 colors. -/
def G4 : Graph 5 := .ofEdges [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

/-- The even cycle `0 - 3 - 4 - 1 - 2 - 5 - 0`. It only needs 2 colors, but in this vertex order
greedy uses all `Δ + 1 = 3` colors. -/
def G5 : Graph 6 := .ofEdges [(0, 3), (3, 4), (4, 1), (1, 2), (2, 5), (5, 0)]

-- *MyNote:* in the following we will pass in the color palette with `d = Δ(G)`
-- using the maximal degree

-- helper to count colors used in result of the greedy algorithm
def countColors {k : ℕ} (c : Vector (Fin k) n) : ℕ := c.toList.dedup.length

-- *Test 0: maximum degree*
example : G1.maxDegree = 0 := rfl  -- empty so zero max degree
example : G2.maxDegree = 2 := rfl  -- a path so at most left/right neighbors
example : G3.maxDegree = 3 := rfl  -- for complete graphs it is always n - 1
example : G4.maxDegree = 2 := rfl  -- same as path case
example : G5.maxDegree = 2 := rfl  -- same as above case

-- *Test 1: correctness*
-- properness check of the coloring returned by greedy
example : IsProperColoring G1 (fun v => (greedyT G1 G1.maxDegree).ret[v]) := by decide
example : IsProperColoring G2 (fun v => (greedyT G2 G2.maxDegree).ret[v]) := by decide
example : IsProperColoring G3 (fun v => (greedyT G3 G3.maxDegree).ret[v]) := by decide
example : IsProperColoring G4 (fun v => (greedyT G4 G4.maxDegree).ret[v]) := by decide
example : IsProperColoring G5 (fun v => (greedyT G5 G5.maxDegree).ret[v]) := by decide

-- check colors used ≤ Δ(G) + 1 on all graphs
example : countColors (greedyT G1 G1.maxDegree).ret ≤ G1.maxDegree + 1 := by decide
example : countColors (greedyT G2 G2.maxDegree).ret ≤ G2.maxDegree + 1 := by decide
example : countColors (greedyT G3 G3.maxDegree).ret ≤ G3.maxDegree + 1 := by decide
example : countColors (greedyT G4 G4.maxDegree).ret ≤ G4.maxDegree + 1 := by decide
example : countColors (greedyT G5 G5.maxDegree).ret ≤ G5.maxDegree + 1 := by decide

-- *Test 2: time*  linear in O(n + m)
-- 🄌 [findFreeT]: ∑ (deg(v) + 1) = 2m + n
-- ➊ [set] & ➌ [reset]: 2m ops per pass
-- ➋ [assign_color]: 1 per vertex and we have n of them

-- Total cost = Cost(🄌 findFreeT) + Cost(➊) + Cost(➋) + Cost(➌)
--            = (n + 2m) + 2m + n + 2m
--            = 2·n + 6·m
example : (greedyT G1 G1.maxDegree).time ≤ 2 * G1.numVertices + 6 * G1.numEdges := by decide
example : (greedyT G2 G2.maxDegree).time ≤ 2 * G2.numVertices + 6 * G2.numEdges := by decide
example : (greedyT G3 G3.maxDegree).time ≤ 2 * G3.numVertices + 6 * G3.numEdges := by decide
example : (greedyT G4 G4.maxDegree).time ≤ 2 * G4.numVertices + 6 * G4.numEdges := by decide
example : (greedyT G5 G5.maxDegree).time ≤ 2 * G5.numVertices + 6 * G5.numEdges := by decide

end Graph

end HW8
