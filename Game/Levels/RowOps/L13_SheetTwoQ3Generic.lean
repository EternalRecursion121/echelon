import Game.Levels.RowOps.L12_SheetTwoQ1f

World "RowOps"
Level 13
Title "A parameter: the generic case"

-- @sheet 2 Q3
/-! @answer
Case $a \ne \pm 1$. $a\rho_1 - \rho_2$ gives $(a^2 - 1)x = a^3 - 1$, i.e.
$(a-1)(a+1)x = (a-1)(a^2+a+1)$; $a\rho_2 - \rho_1$ gives $(a-1)(a+1)y = -a(a-1)$. Since
$a - 1 \ne 0$ and $a + 1 \ne 0$ we may divide: **the unique solution is
$x = \frac{a^2+a+1}{a+1},\ y = \frac{-a}{a+1}$**, and substituting back confirms it.
(The cases $a = 1$ and $a = -1$ are the next level.)
-/
Introduction "
**Problem Sheet 2, Question 3, case $a \\ne \\pm 1$.** Solve, for all $a \\in \\mathbb R$:
$$ax + y = a^2,\\qquad x + ay = 1.$$

Eliminating gives multiples of $a^2 - 1 = (a-1)(a+1)$. Division is allowed only by nonzero
numbers, which is why the answer splits into three cases. This level is the case
$a \\ne 1,\\ a \\ne -1$, given in the form you need: `hp : a + 1 ≠ 0` and `hm : a - 1 ≠ 0`.
The next level is $a = \\pm 1$.

As in level 2 you supply the solution (now formulas in $a$) with `use`.

Useful (Systems tab): `mul_left_cancel₀ hm : (a - 1) * u = (a - 1) * w → u = w`,
`mul_right_cancel₀ hp : u * (a + 1) = w * (a + 1) → u = w`, and
`eq_div_iff hp : u = w / (a + 1) ↔ u * (a + 1) = w`. (The `₀` is typed `\\0`.)
"

namespace LinearAlgebraGame

/-- For $a \ne \pm1$ the system $ax + y = a^2,\ x + ay = 1$ has exactly one solution
$(X, Y)$. -/
Statement (a : ℝ) (hp : a + 1 ≠ 0) (hm : a - 1 ≠ 0) :
    ∃ X Y : ℝ, ∀ x y : ℝ, (a * x + y = a ^ 2 ∧ x + a * y = 1) ↔ (x = X ∧ y = Y) := by
  Hint "Solve on paper (eliminate $y$, then $x$, and divide). `use` your two formulas."
  Hint (hidden := true) "`use (a ^ 2 + a + 1) / (a + 1), -a / (a + 1)`, then `intro x y`."
  use (a ^ 2 + a + 1) / (a + 1), -a / (a + 1)
  intro x y
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    Hint "Eliminate $y$ (combine $a\\rho_1$ and $\\rho_2$), and separately eliminate $x$.
    Write the results with the factor $a - 1$ visible, so that you can cancel it."
    Hint (hidden := true) "`rowop hx : (a - 1) * ((a + 1) * x) = (a - 1) * (a ^ 2 + a + 1) := a * h1 - h2`"
    rowop hx : (a - 1) * ((a + 1) * x) = (a - 1) * (a ^ 2 + a + 1) := a * h1 - h2
    rowop hy : (a - 1) * ((a + 1) * y) = (a - 1) * (-a) := a * h2 - h1
    Hint (hidden := true) "Cancel $a - 1$: `have hx' := mul_left_cancel₀ hm hx`."
    have hx' := mul_left_cancel₀ hm hx
    have hy' := mul_left_cancel₀ hm hy
    Hint (hidden := true) "`constructor`, then `rw [eq_div_iff hp]` and `linear_combination hx'`."
    constructor
    · rw [eq_div_iff hp]
      linear_combination hx'
    · rw [eq_div_iff hp]
      linear_combination hy'
  · intro h
    obtain ⟨hx, hy⟩ := h
    Hint "Clear the denominators in `{hx}`, `{hy}`; then it is enough to check each equation
    multiplied by $a + 1$."
    Hint (hidden := true) "`rw [eq_div_iff hp] at hx hy`, `constructor`, then
    `apply mul_right_cancel₀ hp` and `linear_combination a * hx + hy`."
    rw [eq_div_iff hp] at hx hy
    constructor
    · apply mul_right_cancel₀ hp
      linear_combination a * hx + hy
    · apply mul_right_cancel₀ hp
      linear_combination hx + a * hy

end LinearAlgebraGame

Conclusion "For $a \\ne \\pm 1$ the solution is unique:
$\\left(\\frac{a^2+a+1}{a+1}, \\frac{-a}{a+1}\\right)$."

DisabledTactic linarith nlinarith
NewTheorem mul_right_cancel₀ eq_div_iff mul_left_cancel₀
