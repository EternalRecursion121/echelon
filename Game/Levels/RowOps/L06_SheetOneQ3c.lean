import Game.Levels.RowOps.L05_SheetOneQ3a

World "RowOps"
Level 6
Title "Three equations, four unknowns"

-- @sheet 1 Q3c
/-! @answer
$-2\rho_1 + \rho_2$ gives $y - 2z - 3w = -6$ and $-3\rho_1 + \rho_3$ gives
$y - 2z - 3w = -5$; then $-\rho_2 + \rho_3$ gives $0 = 1$. The system is inconsistent:
**the solution set is empty**.
-/
Introduction "
**Problem Sheet 1, Question 3(c).** Solve using matrix notation:
$$x + z + w = 4,\\quad 2x + y - w = 2,\\quad 3x + y + z = 7.$$

Sometimes Gauss's method produces the row $0 = 1$. Then there is no solution at all.
"

namespace LinearAlgebraGame

/-- The system $x + z + w = 4,\ 2x + y - w = 2,\ 3x + y + z = 7$ has no solution. -/
Statement : ¬ ∃ x y z w : ℝ, x + z + w = 4 ∧ 2 * x + y - w = 2 ∧ 3 * x + y + z = 7 := by
  Hint "Assume a solution: `intro h`, then `obtain ⟨x, y, z, w, h₁, h₂, h₃⟩ := h`."
  intro h
  obtain ⟨x, y, z, w, h₁, h₂, h₃⟩ := h
  Hint "Eliminate $x$ from rows 2 and 3 and compare what is left."
  Hint (hidden := true) "`rowop h₂ : y - 2 * z - 3 * w = -6 := h₂ - 2 * h₁`"
  rowop h₂ : y - 2 * z - 3 * w = -6 := h₂ - 2 * h₁
  Hint (strict := true) (hidden := true) "`rowop h₃ : y - 2 * z - 3 * w = -5 := h₃ - 3 * h₁`"
  rowop h₃ : y - 2 * z - 3 * w = -5 := h₃ - 3 * h₁
  Hint (strict := true) (hidden := true) "`rowop h₃ : (0 : ℝ) = 1 := h₃ - h₂`, then `norm_num at h₃`."
  rowop h₃ : (0 : ℝ) = 1 := h₃ - h₂
  norm_num at h₃

end LinearAlgebraGame

Conclusion "**Answer:** no solution — the solution set is $\\emptyset$."

DisabledTactic linarith nlinarith
