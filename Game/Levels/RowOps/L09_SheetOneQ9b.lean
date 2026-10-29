import Game.Levels.RowOps.L08_SheetOneQ9a

World "RowOps"
Level 9
Title "Gauss–Jordan with a free variable"

-- @sheet 1 Q9b
/-! @answer
$$\left(\begin{array}{ccc|c}1&0&-1&4\\2&2&0&1\end{array}\right)
\xrightarrow{-2\rho_1+\rho_2}\left(\begin{array}{ccc|c}1&0&-1&4\\0&2&2&-7\end{array}\right)
\xrightarrow{\frac12\rho_2}\left(\begin{array}{ccc|c}1&0&-1&4\\0&1&1&-7/2\end{array}\right).$$
$z$ is free, $x = 4 + z$, $y = -7/2 - z$:
$$\left\{\begin{pmatrix}4\\-7/2\\0\end{pmatrix} + z\begin{pmatrix}1\\-1\\1\end{pmatrix}\;\middle|\; z\in\mathbb R\right\}.$$
-/
Introduction "
**Problem Sheet 1, Question 9(b).** Use Gauss–Jordan reduction to solve
$x - z = 4,\\ 2x + 2y = 1$.

The claim states the answer as a parametrised line in $\\mathbb R^3$.
"

namespace LinearAlgebraGame

/-- $x - z = 4,\ 2x + 2y = 1$ iff $(x,y,z) = (4,-7/2,0) + t(1,-1,1)$ for some $t$. -/
Statement (x y z : ℝ) :
    (x - z = 4 ∧ 2 * x + 2 * y = 1) ↔
      ∃ t : ℝ, ![x, y, z] = ![4, -7/2, 0] + t • ![1, -1, 1] := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    Hint "Reduce: $-2\\rho_1 + \\rho_2$ and $\\frac12\\rho_2$. Which variable is free?"
    Hint (hidden := true) "`rowop h2 : y + z = -7/2 := (h2 - 2 * h1) / 2`"
    rowop h2 : y + z = -7/2 := (h2 - 2 * h1) / 2
    Hint (strict := true) (hidden := true) "$z$ is free: `use z`, then compare components."
    use z
    ext i
    fin_cases i
    · norm_num
      linear_combination h1
    · norm_num
      linear_combination h2
    · norm_num
  · intro h
    obtain ⟨t, ht⟩ := h
    have hx := congrFun ht 0
    have hy := congrFun ht 1
    have hz := congrFun ht 2
    norm_num at hx hy hz
    rw [hx, hy, hz]
    constructor
    · linear_combination
    · linear_combination

end LinearAlgebraGame

Conclusion "**Answer:** $\\{(4, -7/2, 0) + z(1, -1, 1) \\mid z \\in \\mathbb R\\}$."

DisabledTactic linarith nlinarith
