import Game.Levels.Echelon.L04_SheetTwoQ9bc

World "Echelon"
Level 5
Title "Computing a reduced echelon form"

-- @sheet 1 Q10
/-! @answer
$$\begin{pmatrix}1&3&1\\2&6&2\\-1&0&0\end{pmatrix}
\xrightarrow[\rho_1+\rho_3]{-2\rho_1+\rho_2}\begin{pmatrix}1&3&1\\0&0&0\\0&3&1\end{pmatrix}
\xrightarrow{\rho_2\leftrightarrow\rho_3}\begin{pmatrix}1&3&1\\0&3&1\\0&0&0\end{pmatrix}
\xrightarrow{\frac13\rho_2}\begin{pmatrix}1&3&1\\0&1&1/3\\0&0&0\end{pmatrix}
\xrightarrow{-3\rho_2+\rho_1}\begin{pmatrix}1&0&0\\0&1&1/3\\0&0&0\end{pmatrix}.$$
The reduced echelon form is $\begin{pmatrix}1&0&0\\0&1&1/3\\0&0&0\end{pmatrix}$.
-/
Introduction "
**Problem Sheet 1, Question 10.** Compute the reduced echelon form of
$\\begin{pmatrix}1&3&1\\\\2&6&2\\\\-1&0&0\\end{pmatrix}$.

The claim: $R = \\begin{pmatrix}1&0&0\\\\0&1&1/3\\\\0&0&0\\end{pmatrix}$ is in reduced echelon
form (Mathlib's `IsReducedRowEchelon`), and is row equivalent to the given matrix. For the
second part, supply $E$, the product of your elementary matrices (rows of $R$ in terms of the
original rows), and its inverse $F$.
"

namespace LinearAlgebraGame

open Matrix in
/-- The reduced echelon form of $\begin{pmatrix}1&3&1\\2&6&2\\-1&0&0\end{pmatrix}$ is
$\begin{pmatrix}1&0&0\\0&1&1/3\\0&0&0\end{pmatrix}$. -/
Statement : (!![1, 0, 0; 0, 1, 1/3; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ).IsReducedRowEchelon ∧
    RowEquiv !![1, 3, 1; 2, 6, 2; -1, 0, 0] !![1, 0, 0; 0, 1, 1/3; 0, 0, 0] := by
  constructor
  · Hint "Three conditions: echelon, leading entries are 1, zeros above leading entries.
    Each is a finite check over rows and columns."
    Hint (hidden := true) "`constructor`, then for each part `intro` the indices, `fin_cases` them,
    and `simp [IsLeadingEntry, Fin.forall_fin_succ] at *`."
    constructor
    · intro i₁ i₂ h j₂ hj
      fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₂ <;> simp [Fin.forall_fin_succ] at h hj ⊢
    · intro i c h
      fin_cases i <;> fin_cases c <;> simp [IsLeadingEntry, Fin.forall_fin_succ] at h ⊢
    · intro i₁ i₂ c h hl
      fin_cases i₁ <;> fin_cases i₂ <;> fin_cases c <;> simp [IsLeadingEntry, Fin.forall_fin_succ] at h hl ⊢
  · Hint "Row 1 of $R$ is $-\\rho_3$, row 2 is $\\frac13(\\rho_1 + \\rho_3)$, row 3 is $\\rho_2 - 2\\rho_1$."
    Hint (hidden := true) "`use !![0, 0, -1; 1/3, 0, 1/3; -2, 1, 0], !![1, 3, 0; 2, 6, 1; -1, 0, 0]`"
    use !![0, 0, -1; 1/3, 0, 1/3; -2, 1, 0], !![1, 3, 0; 2, 6, 1; -1, 0, 0]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> norm_num

end LinearAlgebraGame

Conclusion "**Answer:** $\\begin{pmatrix}1&0&0\\\\0&1&1/3\\\\0&0&0\\end{pmatrix}$."

NewDefinition Matrix.IsReducedRowEchelon
NewTheorem Matrix.IsLeadingEntry Fin.forall_fin_succ
