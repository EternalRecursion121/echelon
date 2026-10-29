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
  · Hint "Name the three rows: `intro h` and `obtain ⟨h1, h2, h3⟩ := h`."
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    Hint (hidden := true) "Eliminate $x$ from rows 2 and 3: `rowop h2 : y + 3 * z = 1 := h2 - 3 * h1`."
    rowop h2 : y + 3 * z = 1 := h2 - 3 * h1
    Hint (strict := true) (hidden := true) "`rowop h3 : y = 4 := h3 + h1`"
    rowop h3 : y = 4 := h3 + h1
    Hint (strict := true) (hidden := true) "Back-substitute: `rowop h2 : z = -1 := (h2 - h3) / 3`."
    rowop h2 : z = -1 := (h2 - h3) / 3
    Hint (strict := true) (hidden := true) "`rowop h1 : x = -1 := h1 + h2`"
    rowop h1 : x = -1 := h1 + h2
    exact ⟨h1, h3, h2⟩
  · Hint "Check the triple: substitute it in."
    intro h
    obtain ⟨hx, hy, hz⟩ := h
    Hint (hidden := true) "`rw [hx, hy, hz]` then `norm_num`."
    rw [hx, hy, hz]
    norm_num

end LinearAlgebraGame

Conclusion "**Answer:** the unique solution is $(x, y, z) = (-1, 4, -1)$."

DisabledTactic linarith nlinarith
