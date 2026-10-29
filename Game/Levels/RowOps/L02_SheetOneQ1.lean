import Game.Levels.RowOps.L01_RowOps

World "RowOps"
Level 2
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

You supply the solution: the claim says there are numbers $a, b, c$ such that the system
holds **if and only if** $x = a$, $y = b$, $z = c$. Start with `use` and your three numbers
(separated by commas, `use a, b, c`), then `intro x y z` (one name per variable).

The direction `→` of the `↔` is Gauss's method (no other triple works); `←` checks your triple
is a solution. `constructor` splits the `↔` (Lean Basics, level 10).
"

namespace LinearAlgebraGame

/-- The system $x - z = 0,\ 3x + y = 1,\ -x + y + z = 4$ has exactly one solution
$(a, b, c)$. -/
Statement : ∃ a b c : ℝ, ∀ x y z : ℝ,
    (x - z = 0 ∧ 3 * x + y = 1 ∧ -x + y + z = 4) ↔ (x = a ∧ y = b ∧ z = c) := by
  Hint "Run Gauss's method on paper first. Which triple do you get? `use` it."
  Hint (hidden := true) "`use -1, 4, -1`, then `intro x y z`."
  use -1, 4, -1
  intro x y z
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
