import Game.Levels.RowOps.L11_SheetTwoQ1e

World "RowOps"
Level 12
Title "A parameter: the generic case"

-- @sheet 2 Q3
/-! @answer
Case $a \ne \pm 1$. $a\rho_1 - \rho_2$ gives $(a^2 - 1)x = a^3 - 1$, i.e.
$(a-1)(a+1)x = (a-1)(a^2+a+1)$; $a\rho_2 - \rho_1$ gives $(a-1)(a+1)y = -a(a-1)$. Since
$a - 1 \ne 0$ and $a + 1 \ne 0$ we may divide: **the unique solution is
$x = \frac{a^2+a+1}{a+1},\ y = \frac{-a}{a+1}$**, and substituting back confirms it.
(The cases $a = 1$ and $a = -1$ are the next two levels.)
-/
Introduction "
**Problem Sheet 2, Question 3, case $a \\ne \\pm 1$.** Solve, for all $a \\in \\mathbb R$:
$$ax + y = a^2,\\qquad x + ay = 1.$$

Eliminating gives multiples of $a^2 - 1 = (a-1)(a+1)$. Division is allowed only by nonzero
numbers, which is why the answer splits into three cases. This level is the case
$a \\ne 1,\\ a \\ne -1$; the next two levels are $a = 1$ and $a = -1$.

Useful: `mul_left_cancel₀ (h : c ≠ 0) : c * a = c * b → a = b`, and
`eq_div_iff (h : c ≠ 0) : a = b / c ↔ a * c = b`.
"

namespace LinearAlgebraGame

/-- For $a \ne \pm1$: $ax + y = a^2,\ x + ay = 1$ iff $x = \frac{a^2+a+1}{a+1},\ y = \frac{-a}{a+1}$. -/
Statement (a : ℝ) (ha1 : a ≠ 1) (ha2 : a ≠ -1) (x y : ℝ) :
    (a * x + y = a ^ 2 ∧ x + a * y = 1) ↔
      (x = (a ^ 2 + a + 1) / (a + 1) ∧ y = -a / (a + 1)) := by
  Hint "First record that $a + 1 \\ne 0$ and $a - 1 \\ne 0$."
  Hint (hidden := true) "`have hp : a + 1 ≠ 0 := by` `intro h` `exact ha2 (by linear_combination h)`"
  have hp : a + 1 ≠ 0 := by
    intro h
    exact ha2 (by linear_combination h)
  have hm : a - 1 ≠ 0 := by
    intro h
    exact ha1 (by linear_combination h)
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    Hint "Eliminate $y$ (linear_combination $a\\rho_1$ and $\\rho_2$), and separately eliminate $x$.
    Write the results with the factor $a - 1$ visible."
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
    Hint "Clear the denominators in `hx`, `hy`, then multiply each goal by $a + 1$."
    rw [eq_div_iff hp] at hx hy
    Hint (hidden := true) "`exact mul_right_cancel₀ hp (by linear_combination a * hx + hy)`"
    constructor
    · exact mul_right_cancel₀ hp (by linear_combination a * hx + hy)
    · exact mul_right_cancel₀ hp (by linear_combination hx + a * hy)

end LinearAlgebraGame

Conclusion "For $a \\ne \\pm 1$ the solution is unique."

DisabledTactic linarith nlinarith
NewTheorem mul_right_cancel₀ eq_div_iff mul_left_cancel₀
