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

Tip: after `have h₀ := congrFun hx 0`, the line
`norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h₀` writes row 0 out as an equation.
"

namespace LinearAlgebraGame

open Matrix in
/-- True or false: every system with more unknowns than equations has a solution. -/
Statement : (¬ ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), m < n → ∃ x, A *ᵥ x = b) ∨
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), m < n → ∃ x, A *ᵥ x = b) := by
  Hint "Can two equations in three unknowns contradict each other?"
  left
  intro h
  Hint (hidden := true) "Try $x + y + z = 0,\\ x + y + z = 1$:
  `obtain ⟨x, hx⟩ := h 2 3 !![1, 1, 1; 1, 1, 1] ![0, 1] (by norm_num)`."
  obtain ⟨x, hx⟩ := h 2 3 !![1, 1, 1; 1, 1, 1] ![0, 1] (by norm_num)
  have h₀ := congrFun hx 0
  have h₁ := congrFun hx 1
  Hint (hidden := true) "`norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h₀ h₁`"
  norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h₀ h₁
  Hint (hidden := true) "`rowop h₁ : (0 : ℝ) = 1 := h₁ - h₀`, then `norm_num at h₁`."
  rowop h₁ : (0 : ℝ) = 1 := h₁ - h₀
  norm_num at h₁

end LinearAlgebraGame

Conclusion "**Answer: false.** $x+y+z = 0,\\ x+y+z = 1$ is a counterexample."

DisabledTactic linarith nlinarith
NewTheorem Fin.sum_univ_three
