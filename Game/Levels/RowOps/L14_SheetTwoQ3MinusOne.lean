import Game.Levels.RowOps.L13_SheetTwoQ3One

World "RowOps"
Level 14
Title "A parameter: a = −1"

-- @sheet 2 Q3
/-! @answer
Case $a = -1$: the equations are $-x + y = 1$ and $x - y = 1$; adding them gives $0 = 2$.
**No solution.**
-/
Introduction "
**Problem Sheet 2, Question 3, case $a = -1$.** Solve $ax + y = a^2,\\ x + ay = 1$ when $a = -1$.
"

namespace LinearAlgebraGame

/-- For $a = -1$ the system has no solution. -/
Statement (a : ℝ) (ha : a = -1) : ¬ ∃ x y : ℝ, a * x + y = a ^ 2 ∧ x + a * y = 1 := by
  intro h
  obtain ⟨x, y, h1, h2⟩ := h
  rw [ha] at h1 h2
  Hint "Add the two rows."
  Hint (hidden := true) "`rowop h2 : (0 : ℝ) = 2 := h1 + h2`, then `norm_num at h2`."
  rowop h2 : (0 : ℝ) = 2 := h1 + h2
  norm_num at h2

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 2 Q3:** $a \\ne \\pm 1$: unique solution
$\\left(\\frac{a^2+a+1}{a+1}, \\frac{-a}{a+1}\\right)$; $a = 1$: infinitely many
(the line $x + y = 1$); $a = -1$: none.
"

DisabledTactic linarith nlinarith
