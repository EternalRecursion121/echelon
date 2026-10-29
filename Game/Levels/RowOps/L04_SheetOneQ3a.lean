import Game.Levels.RowOps.L03_SheetOneQ3b

World "RowOps"
Level 4
Title "A line of solutions"

-- @sheet 1 Q3a
/-! @answer
$$\left(\begin{array}{cc|c}3&6&18\\1&2&6\end{array}\right)
\xrightarrow{-\frac13\rho_1+\rho_2}\left(\begin{array}{cc|c}3&6&18\\0&0&0\end{array}\right),$$
so $y$ is free and $x = 6 - 2y$:
$$\left\{\begin{pmatrix}6\\0\end{pmatrix} + y\begin{pmatrix}-2\\1\end{pmatrix} \;\middle|\; y\in\mathbb R\right\}.$$
-/
Introduction "
**Problem Sheet 1, Question 3(a).** Solve using matrix notation, expressing the solution
using vectors: $3x + 6y = 18,\\ x + 2y = 6$.

When a variable is free the solution set is a line $\\{\\vec p + t\\vec d \\mid t \\in \\mathbb R\\}$.
The claim: there are vectors $\\vec p$ (a particular solution) and $\\vec d$ (the direction)
such that the system holds exactly on that line. You supply $\\vec p$ and $\\vec d$ with `use`.
(`t • d` is the scalar multiple $t\\vec d$; `•` is typed `\\smul`.)

To take apart an \"exists\" hypothesis `h : ∃ t, …`, use `obtain ⟨t, ht⟩ := h` (as in Lean
Basics). At the end you may be left with an equation that is just algebra, such as
`3 * (6 + -(t * 2)) + 6 * t = 18`: `linear_combination` with nothing after it proves any
such identity.
"

namespace LinearAlgebraGame

/-- The solutions of $3x + 6y = 18,\ x + 2y = 6$ form a line $\{\vec p + t\vec d\}$. -/
Statement : ∃ p d : Fin 2 → ℝ, ∀ x y : ℝ,
    (3 * x + 6 * y = 18 ∧ x + 2 * y = 6) ↔ ∃ t : ℝ, ![x, y] = p + t • d := by
  Hint "Row 1 is three times row 2, so one variable is free. Write the solutions as a point
  plus multiples of a direction, and `use` those two vectors."
  Hint (hidden := true) "With $y$ free: `use ![6, 0], ![-2, 1]`, then `intro x y`."
  use ![6, 0], ![-2, 1]
  intro x y
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    Hint "Which $t$ gives the point $(x, y)$?"
    Hint (hidden := true) "If you chose $\\vec p = (6, 0)$, $\\vec d = (-2, 1)$: `use y`, then
    `entrywise` and `norm_num` in each entry."
    use y
    entrywise
    · Hint "The entries are still unevaluated (`(p + t • d) 0` and so on): `norm_num` evaluates
      them first, then the entry is ordinary algebra. (If an entry needs no evaluating, Lean may
      warn that `norm_num` did nothing: harmless.)"
      norm_num
      Hint (hidden := true) "This is row 2 rearranged: `linear_combination h2`."
      linear_combination h2
    · norm_num
  · intro h
    obtain ⟨t, ht⟩ := h
    Hint (hidden := true) "Read off `x` and `y`: `have hx := congrFun {ht} 0`, the same for
    entry 1, `norm_num at hx hy` and `rw [hx, hy]`."
    have hx := congrFun ht 0
    have hy := congrFun ht 1
    norm_num at hx hy
    rw [hx, hy]
    Hint (hidden := true) "Each equation is now an identity in $t$: `constructor`, then
    `linear_combination` (with nothing after it) for each."
    constructor
    · linear_combination
    · linear_combination

end LinearAlgebraGame

Conclusion "**Answer:** $\\{(6,0) + y(-2,1) \\mid y \\in \\mathbb R\\}$ — a line, so infinitely many solutions."

DisabledTactic linarith nlinarith
