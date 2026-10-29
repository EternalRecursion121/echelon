import Game.Levels.RowOps.L06_SheetOneQ3c

World "RowOps"
Level 7
Title "More unknowns than equations"

-- @sheet 1 Q2
/-! @answer
**False.** The system $x + y + z = 0,\ x + y + z = 1$ has three unknowns and only two
equations, but subtracting the first equation from the second gives $0 = 1$, so it has no
solution.
-/
Introduction "
**Problem Sheet 1, Question 2.** True or false: a system with more unknowns than equations
has at least one solution.

A general system of $m$ equations in $n$ unknowns is `A *ᵥ x = b` with
`A : Matrix (Fin m) (Fin n) ℝ`. The goal is `¬ P ∨ P`: commit with `left` (false) or
`right` (true), then prove your choice. To say false you produce a counterexample.

If you assume the claim as `h`, it is a big \"for all\": feed it *your* counterexample, as
in Lean Basics level 12 — `h 2 3 A b (by norm_num)` for a system of 2 equations in 3
unknowns (the `(by norm_num)` proves $2 < 3$).

Tips: `congrFun hx 0` turns an equation of vectors `hx : u = v` into its entry 0,
`u 0 = v 0`; then `norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h0` writes that row out
as an equation (the recipe from Lean Basics, with three unknowns).
"

namespace LinearAlgebraGame

open Matrix in
/-- True or false: every system with more unknowns than equations has a solution. -/
Statement : (¬ ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), m < n → ∃ x, A *ᵥ x = b) ∨
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), m < n → ∃ x, A *ᵥ x = b) := by
  Hint "Decide first: could two equations in three unknowns have no common solution?"
  left
  intro h
  Hint "Pick two equations in three unknowns that contradict each other, and feed them to `{h}`."
  Hint (hidden := true) "Try $x + y + z = 0,\\ x + y + z = 1$:
  `obtain ⟨x, hx⟩ := h 2 3 !![1, 1, 1; 1, 1, 1] ![0, 1] (by norm_num)`."
  obtain ⟨x, hx⟩ := h 2 3 !![1, 1, 1; 1, 1, 1] ![0, 1] (by norm_num)
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  Hint (hidden := true) "`norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1`"
  norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  Hint (hidden := true) "`rowop h1 : 0 = 1 := h1 - h0`, then `norm_num at h1`."
  rowop h1 : 0 = 1 := h1 - h0
  norm_num at h1

end LinearAlgebraGame

Conclusion "**Answer: false.** $x+y+z = 0,\\ x+y+z = 1$ is a counterexample."

DisabledTactic linarith nlinarith
NewTheorem Fin.sum_univ_three
