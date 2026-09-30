/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# Exercise File for Week 2
-- Additional instruction: for every problem, you must supply an informal proof before a Lean proof.
-/

/-
  Recall that sets are defined through membership predicates in Lean
-/
def Set' (α : Type) := α → Prop

namespace Set

variable {α : Type} (A B C : Set α)

/-
# Information
You are allowed to use the following tactics:
  `intro`, `ext`, `exact`, `apply`, `cases`, `obtain`, `left`, `right`, `expose_names`,
  `constructor`, `rewrite`, `rw`, `have`, `rfl`, `assumption`, `contradiction`,
  `by_contra`, `by_cases`, `unfold`, and `use`.
You are also allowed to use local definitions using `let`.
-/

/-
## Hints on using obtain
You can use `obtain` for destructuring conjunctions and existential propositions.
-- For `h : P ∧ Q`, you can write `obtain ⟨hp, hq⟩` to obtain `hp : P` and `hq : Q`
-- For `h : ∃ k : ℕ, P k`, you can write `obtain ⟨k, hk⟩` to obtain `k : ℕ` and `hk : P k`
-/
example (P Q : Prop) (h : P ∧ Q) : P := by
  obtain ⟨hp, hq⟩ := h -- hp : P, hq : Q
  exact hp

example (h : ∃ k : ℕ, k + 1 = 42) : ∃ k : ℕ, k + 1 = 43 := by
  obtain ⟨k, hk⟩ := h -- k : ℕ, hk : k+1 = 42
  use k+1
  rw [hk]

/-
## Hints on using cases
`cases h` eliminates the original hypothesis `h : P ∨ Q` and replaces it in each branch
with a proof of `P` or `Q`. These new proofs may initially have inaccessible names;
`expose_names` makes them usable, you can check the name in the InfoView (often is `h`).
Pattern matching lets you choose clear names such as `hP` and `hQ`.
-/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  · right
    assumption
  · left
    assumption

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h <;> expose_names
  · right
    exact h
  · left
    exact h

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP =>
    right
    exact hP
  | inr hQ =>
    left
    exact hQ

-- **my notes:** In the following, I will reference to some
-- definitions in the book on "Diskrete Mathematik" by Prof. Ueli Maurer
-- https://crypto.ethz.ch/teaching/DM24/

/-
  Exercise 1:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.

  **my informal proof:**
  By set extensionality, denote for arbitrary element `x` we have
             (A ∩ B) ∪ C =     (A ∪ C) ∩ (B ∪ C)
  ⇔ ∀ x (x ∈ (A ∩ B) ∪ C ↔ x ∈ (A ∪ C) ∩ (B ∪ C))  | axiom of extensionality (3.2)

  We prove the overall statement by proving the two directions of implications separately.

  · (→) prove x ∈ (A ∩ B) ∪ C → x ∈ (A ∪ C) ∩ (B ∪ C)
      From the assumption, by applying definition of union of sets directly
            x ∈ (A ∩ B) ∪ C
          ⇔ x ∈ (A ∩ B) ∨ x ∈ C               | def. set union (3.4)

      This allows us to do a case distinction (denoted below as cases 1.1, 1.2)
      · case 1.1: assume x ∈ (A ∩ B)
            x ∈ (A ∩ B)
          ⇔ x ∈ A ∧ x ∈ B                     | def. set intersection (3.4)

        Before using the assumptions, observe that the statement to
        prove can be rewritten as follows:
            x ∈ (A ∪ C) ∩ (B ∪ C)
          ⇔ x ∈ (A ∪ C) ∧ x ∈ (B ∪ C)         | def. set intersection (3.4)
          ⇔ (x ∈ A ∨ x ∈ C) ∧ (x ∈ B ∨ x ∈ C) | def. set union (3.4)
                    |                    |
                    ①                   ②
        We see the left of the disjunction formula ① is fulfilled by assumption x ∈ A,
        the left of the disjunction formula ② is fulfilled by assumption x ∈ C

      · case 1.2: assume x ∈ C
        This direction is easier and we may apply the assumption directly,
        for disjunction formula ①, the right formula is fulfilled by assumption x ∈ C;
        for disjunction formula ②, the right formula is fulfilled by assumption x ∈ C


  · (←) prove x ∈ (A ∪ C) ∩ (B ∪ C) → x ∈ (A ∩ B) ∪ C
        From the assumption,
        x ∈ (A ∪ C) ∩ (B ∪ C)
      ⇔ x ∈ (A ∪ C) ∧ x ∈ (B ∪ C)             | def. set intersection (3.4)
      ⇔ (x ∈ A ∨ x ∈ C) ∧ (x ∈ B ∨ x ∈ C)     | def. set union (3.4)
                  |               |
                  ③              ④

        Before we continue, we rewrite the goal statement using set union,
        x ∈ (A ∩ B) ∪ C
      ⇔ x ∈ (A ∩ B) ∨ x ∈ C                   | def. set union (3.4)

        Now we see only one of the above formula in disjunction needs to be fulfilled;
        To verify this, we perform case distinction on assumptions, i.e. formulas within ③, ④.

        Consider the left formula within the conjunction formula ③
        · case 2.1: x ∈ A assumed, then for this fixed choice of ③, two other case distinctions
          need to be considered for the formula ④ (x ∈ B ∨ x ∈ C)
          · case 2.1.1: x ∈ B assumed, we recognize it shall fulfill the
              left of the goal, i.e., x ∈ (A ∩ B) by direct use of assumptions
          · case 2.1.2: x ∈ C assumed, then we see the right of the goal, i.e.,
          x ∈ C is directly fulfilled by use of assumption

        Or consider the right formula within ③:
        · case 2.2: x ∈ C assumed, then again the right of the goal, i.e.
          x ∈ C is directly fulfilled by use of assumption
-/
theorem Q1 : (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := by
  ext x
  constructor
  -- (→) direction: x ∈ (A ∩ B) ∪ C → x ∈ (A ∪ C) ∩ (B ∪ C)
  · intro lhs
    -- we need to examine two assumptions to show they both lead
    -- to the same desired result, intuitively, under disjunction x may land on either parts
    rw [Set.union_def] at lhs -- not explicitly needed but we add it here to match informal proof
    cases lhs with
    -- case 1.1: assume x ∈ (A ∩ B)
    | inl hab =>
      rw [mem_inter_iff] at hab
      obtain ⟨ha, hb⟩ := hab
      constructor
      · left; assumption
      · left; assumption
    -- case 1.2: assume x ∈ C
    | inr hc =>
      constructor
      · right; assumption
      · right; assumption
  -- (←) direction: x ∈ (A ∪ C) ∩ (B ∪ C) → x ∈ (A ∩ B) ∪ C
  · intro lhs
    obtain ⟨hac, hbc⟩ := lhs
    rw [Set.union_def] at hac
    rw [Set.union_def] at hbc
    -- case 2: (x ∈ A) ∨ (x ∈ C)
    cases hac with
    -- case 2.1: x ∈ A
    | inl ha =>
      cases hbc with
      -- case 2.1.1: x ∈ B
      | inl hb =>
        left
        exact ⟨ha, hb⟩
      -- case 2.1.2: x ∈ C
      | inr hc => right; assumption
    -- case 2.2: x ∈ C
    -- if x ∈ C, we are done
    | inr hc => right; assumption

/-
  We define the operation of the symmetric difference on sets.
-/
def symm_diff (A B : Set α) : Set α :=
  (A \ B) ∪ (B \ A)

notation A " ∆ " B => Set.symm_diff A B

#check symm_diff

/-
  Exercise 2:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.

  **my informal proof:**
  We only need to prove one direction,
      x ∈ A ∩ (B ∆ C) → x ∈ (A ∩ B) ∆ (A ∩ C)

  In the following we expand the symmetric difference in the
  goal statement implicitly and have used:
      x ∈ (A ∩ B) ∆ (A ∩ C)
    ⇔ x ∈ ((A ∩ B) \ (A ∩ C)) ∪ ((A ∩ C) \ (A ∩ B))     | def. set union (3.4)
    ⇔ x ∈ ((A ∩ B) \ (A ∩ C)) ∨ x ∈ ((A ∩ C) \ (A ∩ B))
              |                   |
            `left`                 `right`

  In the proof below, either left or the right of the above disjunction formula
  needs to be satisfied.

  (→) Starting from the assumption,
      x ∈ A ∩ (B Δ C)
    ⇔ x ∈ A ∧ x ∈ (B Δ C)                   | def. set intersection (3.4)
    ⇔ x ∈ A ∧ x ∈ (B \ C) ∪ (C \ B)         | def. symmetric difference
    ⇔ x ∈ A ∧ (x ∈ (B \ C) ∨ x ∈ (C \ B))   | def. set union (3.4)
        |          |
        A.1        A.2

      Examining the formula x ∈ (B \ C) ∪ (C \ B), i.e. (A.2) in the assumptions,
      leads us to the case distinction, where
      · case 1: x ∈ (B \ C) ⇔ x ∈ B ∧ x ∉ C assumed, the `left` of goal
        is x ∈ ((A ∩ B) \ (A ∩ C)) as conjunction is involved in definition
        of set difference, the goal breaks down to two subgoals:
          · subgoal 1.1: x ∈ (A ∩ B); which is satisfied by assumption A.1 (x ∈ A)
            in conjunction with (x ∈ B) in the assumption.
          · subgoal 1.2: x ∉ (A ∩ C);
            If by contradiction that x ∈ (A ∩ C), i.e. x ∈ A ∧ x ∈ C,
            we see such x ∈ C contradicts x ∉ C in the overall assumption
            of case 1.
        Thus, x ∈ (A ∩ B) ∆ (A ∩ C) is fulfilled and closes case 1.

      · case 2: x ∈ (C \ B) ⇔ x ∈ C ∧ x ∉ B assumed, the `right` of goal
        is now x ∈ ((A ∩ C) \ (A ∩ B)), we break it down to
          · subgoal 2.1: x ∈ (A ∩ C); satisfied by A.1 (x ∈ A)
            in conjunction with (x ∈ C).
          · subgoal 2.2: x ∉ (A ∩ B);
            If by contradiction that x ∈ (A ∩ B), i.e. x ∈ A ∧ x ∈ B,
            such x ∈ B contradicts x ∉ B in the overall assumption of case 2.
        Again x ∈ (A ∩ B) ∆ (A ∩ C) is fulfilled and closes case 2.
-/
theorem Q2 (x : α) : x ∈ A ∩ (B ∆ C) → x ∈ (A ∩ B) ∆ (A ∩ C) := by
  intro lhs
  obtain ⟨ha, hbc⟩ := lhs
  rw [symm_diff] at hbc
  rw [Set.union_def] at hbc
  cases hbc with
  -- case 1: we assume x ∈ B \ C
  -- accordingly the appropriate "goal" would be the x ∈ (A ∩ B) \ (A ∩ C)
  | inl hb_diff =>
    left
    obtain ⟨hb, hnc⟩ := hb_diff
    constructor
    -- subgoal 1.1: x ∈ (A ∩ B)
    · exact ⟨ha, hb⟩
    -- subgoal 1.2: x ∉ (A ∩ C)
    · by_contra
      obtain ⟨_, hc⟩ := this
      contradiction
  -- case 2: we assume x ∈ (C \ B)
  | inr hc_diff =>
    right
    obtain ⟨hc, hnb⟩ := hc_diff
    constructor
    -- subgoal 2.1: x ∈ A ∩ C
    · exact ⟨ha, hc⟩
    -- subgoal 2.2: x ∉ A ∩ B
    · by_contra
      obtain ⟨ha, hb⟩ := this
      contradiction

/-
  Exercise 3:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.

  Hint: the following theorems may be helpful.
-/
#check Set.mem_union          -- x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b
#check Set.mem_inter          -- x ∈ a → x ∈ b → x ∈ a ∩ b
#check Set.mem_sdiff          -- x ∈ s \ t ↔ x ∈ s ∧ x ∉ t
#check Set.mem_compl_iff      -- x ∈ sᶜ ↔ x ∉ s
#check Set.notMem_compl_iff   -- x ∉ sᶜ ↔ x ∈ s
#check Iff.mp                 -- (a ↔ b) → a → b
#check Iff.mpr                -- (a ↔ b) → b → a

-- **my change in the style of informal proofs...**
-- *Hi TA(s).. since the previous way of using DiskMath-like proofs took so much time*
-- *and adding that the new moodle announcement provided the `example.lean`-like*
-- *example of informal proof, we decided to continue using the option 2 from now on,*
-- *to save some time 🙂*

/-
  **my informal proof:**
  - First, by set extensionality the goal becomes "membership checks" x ∈ A ∆ B ↔ x ∈ Aᶜ ∆ Bᶜ.
  - Second, split the equivalence into two directions to close separately
  - Within each direction the assumption involves use of a symmetric difference,
          which requires us to do a case split on the membership of x
    - (→) direction: TODO

    use definition of set difference, we see
    - (←) direction:
-/
theorem Q3 : (A ∆ B) = Aᶜ ∆ Bᶜ := by
  ext x
  constructor
  -- (→) direction: x ∈ A \ B ∪ B \ A → x ∈ Aᶜ \ Bᶜ ∪ Bᶜ \ Aᶜ
  · intro lhs
    cases lhs with
    | inl ha_nb =>
      obtain ⟨ha, hnb⟩ := ha_nb
      right
      --  `x ∉ sᶜ ↔ x ∈ s`
      exact ⟨hnb, Iff.mpr notMem_compl_iff ha⟩
    | inr hb_na =>
      obtain ⟨hb, hna⟩ := hb_na
      left
      exact ⟨hna, Iff.mpr notMem_compl_iff hb⟩
  -- (←) direction: x ∈ Aᶜ \ Bᶜ ∪ Bᶜ \ Aᶜ → x ∈ A \ B ∪ B \ A
  · intro lhs
    cases lhs with
    | inl hnab =>
      obtain ⟨hna, hb⟩ := hnab
      right
      exact ⟨Iff.mp notMem_compl_iff hb, hna⟩
    | inr hnba =>
      obtain ⟨hnb, ha⟩ := hnba
      left
      exact ⟨Iff.mp notMem_compl_iff ha, hnb⟩


/-!
  Exercise 4:

  Prove the following theorems.
  You may only use the tactics stated at the start of the sheet.
  You can use Q4a and Q4b for Q4c, even if you have not proven them.
-/

-- The following theorems may be helpful
#check empty_sdiff -- ∅ \ s = ∅
#check empty_inter -- ∅ ∩ a = ∅
#check empty_union -- ∅ ∪ a = a

#check sdiff_empty -- s \ ∅ = s
#check inter_empty -- a ∩ ∅ = ∅
#check union_empty -- a ∪ ∅ = a

#check sdiff_self -- s \ s = ∅
#check inter_self -- a ∩ a = a
#check union_self -- a ∪ a = a

-- You can use also the following theorem
theorem symm_diff_assoc : ((A ∆ B) ∆ C) = (A ∆ (B ∆ C)) := by
  unfold symm_diff
  grind -- `grind` is a powerful tactic, but you are not allowed to use it yet

/-
  **my informal proof:** for sets that do not intersect, their symmetric
  difference is just union TODO
#check empty_sdiff -- ∅ \ s = ∅
#check sdiff_empty -- s \ ∅ = s
-/
theorem Q4a : (∅ ∆ A) = A := by
  ext x
  constructor
  -- subgoal 1: (x ∈ ∅ ∆ A) → x ∈ A
  · intro lhs
    cases lhs with
    | inl h_emp_na =>
      rw [empty_sdiff] at h_emp_na
      contradiction
    | inr h_a_nemp =>
      rw [sdiff_empty] at h_a_nemp
      assumption
  -- subgoal 2: x ∈ A → x ∈ ∅ ∆ A
  · intro lhs
    right
    rw [sdiff_empty]
    assumption
/-
  **my informal proof:**
  · By extensionality, for arbitrary element `x` we
  rewrite the equality to set membership statements and break
  them into a two-directional subgoals to prove.
  · *subgoal 1:* (x ∈ A ∆ A) → x ∈ ∅
    By definition of symmetric difference, the assumption
    boils down to x ∈ (A \ A) ∪ (A \ A), then by lemma (s \ s = ∅),
    i.e. the self set difference gives rise to an empty set, we are
    essentially taking the union of two empty sets. By lemma (∅ ∪ a = a),
    the overall assumption becomes x ∈ ∅, which now directly closes the
    goal.
  · *subgoal 2:* x ∈ ∅ → x ∈ A ∆ A
    Use the definition of symmetric difference, the goal rewrites to
    a union of the same set with itself `x ∈ (A \ A) ∪ (A \ A)`. We may pick either
    one to proceed the proof.
    Pick left of disjunction and aim to prove `x ∈ (A \ A)`.
    By using self set difference lemma (s \ s = ∅), the goal
    rewrites to `x ∈ ∅`, which is directly satisfied by assumption.
-/
theorem Q4b : (A ∆ A) = ∅ := by
  ext x
  constructor
  · intro lhs
    rw [symm_diff] at lhs
    rw [sdiff_self] at lhs
    rw [empty_union] at lhs
    assumption
  · intro lhs
    rw [symm_diff]
    left
    rw [sdiff_self]
    assumption

/-
  **my informal proof:**
  · First, we follow the given notation and call the sets A, B;
    we want to construct a set C such that it solves (A ∆ C) = B
  · We construct C := A Δ B, and aim to show (A ∆ (A Δ B)) = B
  · By associativity of symmetric difference ((A ∆ B) ∆ C) = (A ∆ (B ∆ C)) holds,
    note our target is RHS of the above equality, which is equivalent to
       ((A ∆ A) Δ B) = B
     ⇔       (∅ Δ B) = B  | Q4b
     ⇔             B = B  | Q4a
    In the last two steps we applied the theorems Q4b, Q4a we proved above
    and closed the proof by reflexivity.
-/
theorem Q4c : ∀ A : Set ℕ, ∀ B : Set ℕ, ∃ C : Set ℕ, (A ∆ C) = B := by
  intro A B
  use symm_diff A B      -- for the existence proof, use C := A Δ B
  -- infoview shows goal ⊢ (A ∆ A ∆ B) = B
  -- right associative default, thus ⊢ (A ∆ (A ∆ B)) = B
  -- we need to apply `symm_diff_assoc` starting from the RHS of the equation
  rw [← symm_diff_assoc] -- symm_diff_assoc : ((A ∆ B) ∆ C) = (A ∆ (B ∆ C))
  rw [Q4b] -- Q4b: (A ∆ A) = ∅
  rw [Q4a] -- Q4a: (∅ ∆ A) = A

end Set

namespace Asymptotics

/-
  Consider the following definition of big-O-notation.
-/
def inBigO (f g : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, f n ≤ c * g n

def BigO (g : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {f : ℕ → ℕ | inBigO f g}

notation "O(" g ")" => BigO g

#check inBigO
#check BigO

/-
  Hint: The following theorems may be helpful.
-/
#check Set.mem_ofPred_eq   -- (x ∈ {y | p y}) = p x
#check zero_lt_one         -- 0 < 1
#check one_mul             --  1 * a = a

/-
  Exercise 5:

  Prove the following theorem.
  You may only use the tactics stated at the start of the sheet.

  **my informal proof:**
  · First, unfold the goal by definitions of big-O `O(g)` of a function `g`;
    then we further use (x ∈ {y | p y}) = p x to simplify to a predicate expression
  · Then to satisfies the existence condition. We may pick some constant `c = 1`.
    Intuitively, we want to show the growth rate of a function cannot exceed itself.
  · The introduction of the constant `c` splits the overall goal into two subgoals:
      · *subgoal 1:* such a constant must be positive, which is fulfilled since
        the assumption fulfills `0 < 1`
      · *subgoal 2:* now we need to pick a starting index n₀, and to fulfill the predicate
        for arbitrary `n` that for all such subsequent indices the inequality
        g(n) ≤ 1 * g(n) holds. We notice `1` is a multiplicative identity element and
        thus g(n) ≤ g(n), we then conclude the proof by reflexivity.
-/
theorem Q5 (g : ℕ → ℕ) : g ∈ O(g) := by
  unfold BigO inBigO
  rw [Set.mem_ofPred_eq]
  use 1
  constructor
  -- subgoal 1: 0 < 1
  · exact zero_lt_one
  -- subgoal 2: ∃ n₀, ∀ n ≥ n₀, g n ≤ 1 * g n
  · use 0
    intro n hn         -- split out predicate in goal
    rewrite [one_mul]  -- rewrite RHS of goal in form `g n ≤ g n`
    rfl

end Asymptotics
