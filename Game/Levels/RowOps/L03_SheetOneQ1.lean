import Game.Levels.RowOps.L02_RowOp

World "RowOps"
Level 3
Title "The unique solution"

-- @sheet 1 Q1
/-! @answer
$-3\rho_1 + \rho_2$ gives $y + 3z = 1$; $\rho_1 + \rho_3$ gives $y = 4$. Back-substituting,
$3z = 1 - 4$, so $z = -1$, and $x = z = -1$. Conversely $(x,y,z) = (-1, 4, -1)$ satisfies all
three equations, so it is **the unique solution $(x, y, z) = (-1, 4, -1)$**.
-/
Introduction "
**Problem Sheet 1, Question 1.** Use Gauss's Method to find the unique solution of
$$x - z = 0,\\quad 3x + y = 1,\\quad -x + y + z = 4.$$

\"The unique solution is $(-1, 4, -1)$\" is an *if and only if*: the system holds **iff**
$x = -1$, $y = 4$, $z = -1$. The direction `→` (Gauss's method) says no other triple works;
`←` checks the triple is a solution. `constructor` splits the `↔`.
"

namespace LinearAlgebraGame

/-- $x - z = 0,\ 3x + y = 1,\ -x + y + z = 4$ holds iff $(x,y,z) = (-1,4,-1)$. -/
Statement (x y z : ℝ) :
    (x - z = 0 ∧ 3 * x + y = 1 ∧ -x + y + z = 4) ↔ (x = -1 ∧ y = 4 ∧ z = -1) := by
  Hint "Split the `↔` with `constructor`."
  constructor
  · Hint "Name the three rows: `intro h` and `obtain ⟨h₁, h₂, h₃⟩ := h`."
    intro h
    obtain ⟨h₁, h₂, h₃⟩ := h
    Hint (hidden := true) "Eliminate $x$ from rows 2 and 3: `rowop h₂ : y + 3 * z = 1 := h₂ - 3 * h₁`."
    rowop h₂ : y + 3 * z = 1 := h₂ - 3 * h₁
    Hint (strict := true) (hidden := true) "`rowop h₃ : y = 4 := h₃ + h₁`"
    rowop h₃ : y = 4 := h₃ + h₁
    Hint (strict := true) (hidden := true) "Back-substitute: `rowop h₂ : z = -1 := (h₂ - h₃) / 3`."
    rowop h₂ : z = -1 := (h₂ - h₃) / 3
    Hint (strict := true) (hidden := true) "`rowop h₁ : x = -1 := h₁ + h₂`"
    rowop h₁ : x = -1 := h₁ + h₂
    exact ⟨h₁, h₃, h₂⟩
  · Hint "Check the triple: substitute it in."
    intro h
    obtain ⟨hx, hy, hz⟩ := h
    Hint (hidden := true) "`rw [hx, hy, hz]` then `norm_num`."
    rw [hx, hy, hz]
    norm_num

end LinearAlgebraGame

Conclusion "**Answer:** the unique solution is $(x, y, z) = (-1, 4, -1)$."

DisabledTactic linarith nlinarith
