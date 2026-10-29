import Game.Levels.RowOps.L04_SheetOneQ3b

World "RowOps"
Level 5
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

The claim below is the answer: the solutions are exactly the vectors
$\\begin{pmatrix}6\\\\0\\end{pmatrix} + t\\begin{pmatrix}-2\\\\1\\end{pmatrix}$.
"

namespace LinearAlgebraGame

/-- $3x + 6y = 18,\ x + 2y = 6$ iff $(x,y) = (6,0) + t(-2,1)$ for some $t$. -/
Statement (x y : ℝ) :
    (3 * x + 6 * y = 18 ∧ x + 2 * y = 6) ↔ ∃ t : ℝ, ![x, y] = ![6, 0] + t • ![-2, 1] := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    Hint "Row 1 is three times row 2, so $y$ is free. Which $t$ gives the point $(x, y)$?"
    Hint (hidden := true) "`use y`, then compare components."
    use y
    ext i
    fin_cases i
    · norm_num
      Hint (hidden := true) "This is row 2 rearranged: `linear_combination h2`."
      linear_combination h2
    · norm_num
  · intro h
    obtain ⟨t, ht⟩ := h
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
