import Game.Levels.RowOps.L07_SheetOneQ2

World "RowOps"
Level 8
Title "Gauss–Jordan, two by two"

-- @sheet 1 Q9a
/-! @answer
$$\left(\begin{array}{cc|c}1&1&2\\1&-1&0\end{array}\right)
\xrightarrow{-\rho_1+\rho_2}\left(\begin{array}{cc|c}1&1&2\\0&-2&-2\end{array}\right)
\xrightarrow{-\frac12\rho_2}\left(\begin{array}{cc|c}1&1&2\\0&1&1\end{array}\right)
\xrightarrow{-\rho_2+\rho_1}\left(\begin{array}{cc|c}1&0&1\\0&1&1\end{array}\right),$$
so **$(x, y) = (1, 1)$**.
-/
Introduction "
**Problem Sheet 1, Question 9(a).** Use Gauss–Jordan reduction to solve
$x + y = 2,\\ x - y = 0$.

Gauss–Jordan keeps going until every leading entry is $1$ with zeros above it: each
`rowop` should leave a row of the reduced form. As in level 3, supply the solution with `use`.
"

namespace LinearAlgebraGame

/-- The system $x + y = 2,\ x - y = 0$ has exactly one solution $(a, b)$. -/
Statement : ∃ a b : ℝ, ∀ x y : ℝ, (x + y = 2 ∧ x - y = 0) ↔ (x = a ∧ y = b) := by
  Hint "Reduce on paper first and `use` the solution you find."
  Hint (hidden := true) "`use 1, 1`, then `intro x y` and `constructor`."
  use 1, 1
  intro x y
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    Hint "Eliminate below the first leading entry, make the second leading entry $1$, then
    clear above it."
    Hint (hidden := true) "$-\\rho_1 + \\rho_2$, $-\\frac12\\rho_2$, $-\\rho_2 + \\rho_1$:
    `rowop h2 : -2 * y = -2 := h2 - h1`, …"
    rowop h2 : -2 * y = -2 := h2 - h1
    rowop h2 : y = 1 := h2 / (-2)
    rowop h1 : x = 1 := h1 - h2
    exact ⟨h1, h2⟩
  · intro h
    obtain ⟨hx, hy⟩ := h
    rw [hx, hy]
    norm_num

end LinearAlgebraGame

Conclusion "**Answer:** $(x, y) = (1, 1)$."

DisabledTactic linarith nlinarith
