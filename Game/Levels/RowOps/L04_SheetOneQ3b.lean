import Game.Levels.RowOps.L03_SheetOneQ1

World "RowOps"
Level 4
Title "Two lines that cross"

-- @sheet 1 Q3b
/-! @answer
$$\left(\begin{array}{cc|c}1&1&1\\1&-1&-1\end{array}\right)
\xrightarrow{-\rho_1+\rho_2}\left(\begin{array}{cc|c}1&1&1\\0&-2&-2\end{array}\right),$$
so $y = 1$ and $x = 0$: the solution set is $\left\{\begin{pmatrix}0\\1\end{pmatrix}\right\}$.
-/
Introduction "
**Problem Sheet 1, Question 3(b).** Solve using matrix notation, expressing the solution
using vectors: $x + y = 1,\\ x - y = -1$.

We write the answer as a vector equation `![x, y] = ![0, 1]`. To prove two vectors equal,
`ext i` and `fin_cases i`; `norm_num` then reads off the component.
"

namespace LinearAlgebraGame

/-- $x + y = 1,\ x - y = -1$ iff $(x, y) = (0, 1)$. -/
Statement (x y : ℝ) : (x + y = 1 ∧ x - y = -1) ↔ ![x, y] = ![0, 1] := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := h
    Hint "Eliminate $x$ from the second row."
    Hint (hidden := true) "`rowop h₂ : y = 1 := (h₁ - h₂) / 2`"
    rowop h₂ : y = 1 := (h₁ - h₂) / 2
    rowop h₁ : x = 0 := h₁ - h₂
    Hint (hidden := true) "`ext i`, `fin_cases i`, then in each case `norm_num` and `exact`."
    ext i
    fin_cases i
    · norm_num
      exact h₁
    · norm_num
      exact h₂
  · intro h
    Hint "Read off the two components of `h` with `congrFun h 0` and `congrFun h 1`."
    have hx := congrFun h 0
    have hy := congrFun h 1
    Hint (hidden := true) "`norm_num at hx hy`, then `rw [hx, hy]` and `norm_num`."
    norm_num at hx hy
    rw [hx, hy]
    norm_num

end LinearAlgebraGame

Conclusion "**Answer:** the single vector $(0, 1)$."

TheoremTab "Vectors"

DisabledTactic linarith nlinarith
NewTheorem congrFun
