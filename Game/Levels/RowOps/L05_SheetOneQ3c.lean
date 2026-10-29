import Game.Levels.RowOps.L04_SheetOneQ3a

World "RowOps"
Level 5
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

First decide: does this system have a solution at all? The goal is `¬ P ∨ P` with `P` =
\"there is a solution\": commit with `left` (no solution) or `right` (there is one), as in
Lean Basics. To prove there is none, assume a solution and run Gauss's method until a row
says something false. You can state such a row yourself, e.g. `rowop h3 : 0 = 1 := …`.
"

namespace LinearAlgebraGame

/-- Does $x + z + w = 4,\ 2x + y - w = 2,\ 3x + y + z = 7$ have a solution? -/
Statement : (¬ ∃ x y z w : ℝ, x + z + w = 4 ∧ 2 * x + y - w = 2 ∧ 3 * x + y + z = 7) ∨
    (∃ x y z w : ℝ, x + z + w = 4 ∧ 2 * x + y - w = 2 ∧ 3 * x + y + z = 7) := by
  Hint "Run Gauss's method on paper first, then commit."
  left
  Hint "Assume a solution: `intro h`, then `obtain ⟨x, y, z, w, h1, h2, h3⟩ := h`."
  intro h
  obtain ⟨x, y, z, w, h1, h2, h3⟩ := h
  Hint "Eliminate $x$ from rows 2 and 3 and compare what is left."
  Hint (hidden := true) "`rowop h2 : y - 2 * z - 3 * w = -6 := h2 - 2 * h1`"
  rowop h2 : y - 2 * z - 3 * w = -6 := h2 - 2 * h1
  Hint (strict := true) (hidden := true) "`rowop h3 : y - 2 * z - 3 * w = -5 := h3 - 3 * h1`"
  rowop h3 : y - 2 * z - 3 * w = -5 := h3 - 3 * h1
  Hint (strict := true) (hidden := true) "`rowop h3 : 0 = 1 := h3 - h2`, then `norm_num at h3`."
  rowop h3 : 0 = 1 := h3 - h2
  norm_num at h3

end LinearAlgebraGame

Conclusion "**Answer:** no solution — the solution set is $\\emptyset$."

DisabledTactic linarith nlinarith
