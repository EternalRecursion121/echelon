import Game.Levels.RowOps.L12_SheetTwoQ3Generic

World "RowOps"
Level 13
Title "A parameter: a = 1"

-- @sheet 2 Q3
/-! @answer
Case $a = 1$: both equations read $x + y = 1$, so $y$ is free and the solution set is
**$\{(1, 0) + t(-1, 1) \mid t \in \mathbb R\}$ — infinitely many solutions**.
-/
Introduction "
**Problem Sheet 2, Question 3, case $a = 1$.** Solve $ax + y = a^2,\\ x + ay = 1$ when $a = 1$.
"

namespace LinearAlgebraGame

/-- For $a = 1$: the solutions are $(1,0) + t(-1,1)$. -/
Statement (a : ℝ) (ha : a = 1) (x y : ℝ) :
    (a * x + y = a ^ 2 ∧ x + a * y = 1) ↔ ∃ t : ℝ, ![x, y] = ![1, 0] + t • ![-1, 1] := by
  Hint "Substitute $a = 1$ first: `rw [ha]`."
  rw [ha]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    Hint "The two rows are the same equation. Which variable is free?"
    use y
    ext i
    fin_cases i
    · norm_num
      linear_combination h2
    · norm_num
  · intro h
    obtain ⟨t, ht⟩ := h
    have hx := congrFun ht 0
    have hy := congrFun ht 1
    norm_num at hx hy
    rw [hx, hy]
    constructor
    · linear_combination
    · linear_combination

end LinearAlgebraGame

Conclusion "For $a = 1$: infinitely many solutions."

DisabledTactic linarith nlinarith
