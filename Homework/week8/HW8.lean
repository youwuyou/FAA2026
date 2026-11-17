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
def IsProperColoring {n k : ℕ} (g : Graph n) (c : Coloring n k) : Prop :=
  ∀ v, ∀ u ∈ g.adj v, c u ≠ c v

-- here we use the existence statement in order to tie a concrete coloring to a proposition
def Colorable {n : ℕ} (k : ℕ) (g : Graph n) : Prop :=
  ∃ c : Coloring n k, IsProperColoring g c

-- *derived properties of the graph*
def degree (v : Fin n) (g : Graph n) : ℕ := (g.adj v).length
def maxDegree (g : Graph n) : ℕ := Finset.univ.sup g.degree

-- *algorithm*

-- *correctness (Optional)*
-- the maximum degree `Δ(G)`
-- the size of the input?

-- * Implement the greedy algorithm in `TimeM`. `TimeM` only counts the ticks that you write, so
--   choose a cost model that describes what your algorithm would cost on a real computer, and
--   explain in a comment for every tick which operations it pays for.

-- * (Optional) Prove that your algorithm computes a proper coloring with `Δ(G) + 1` colors.

-- *computational cost (Optional)*
-- *Prove that your algorithm runs in linear time.
-- * Implement the greedy algorithm in `TimeM`. `TimeM` only counts the ticks that you write, so
--   choose a cost model that describes what your algorithm would cost on a real computer, and
--   explain in a comment for every tick which operations it pays for.

-- *test on graphs*
-- * Test your algorithm on a few graphs.

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

end Graph

end HW8
