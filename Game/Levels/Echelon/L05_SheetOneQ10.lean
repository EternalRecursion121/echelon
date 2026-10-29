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

The claim: there is a matrix $R$ in reduced echelon form (Mathlib's `IsReducedRowEchelon`)
that is row equivalent to the given matrix. Since the reduced echelon form is unique, only the
right answer works. Compute $R$ on paper and supply it with `use`.

Checking that $R$ is reduced echelon is a finite check: `constructor` splits it into its three
conditions (echelon — `IsRowEchelon` —, leading entries $1$, zeros above them), and
`simp [IsRowEchelon, IsLeadingEntry, Fin.forall_fin_succ]` checks a condition by running
through all rows and columns. For `RowEquiv`, supply $E$ (row $i$ of $E$ says which combination
of the original rows gives row $i$ of $R$) and $F$, which undoes $E$.
"

namespace LinearAlgebraGame

open Matrix in
/-- The matrix $\begin{pmatrix}1&3&1\\2&6&2\\-1&0&0\end{pmatrix}$ is row equivalent to a
reduced echelon matrix $R$. -/
Statement : ∃ R : Matrix (Fin 3) (Fin 3) ℝ,
    R.IsReducedRowEchelon ∧ RowEquiv !![1, 3, 1; 2, 6, 2; -1, 0, 0] R := by
  Hint "Run Gauss–Jordan on paper and `use` the reduced echelon form you get."
  Hint (hidden := true) "`use !![1, 0, 0; 0, 1, 1/3; 0, 0, 0]`, then `constructor`."
  use !![1, 0, 0; 0, 1, 1/3; 0, 0, 0]
  constructor
  · Hint "Three conditions: echelon, leading entries are 1, zeros above leading entries.
    Each is a finite check over rows and columns."
    Hint (hidden := true) "`constructor <;> simp [IsRowEchelon, IsLeadingEntry, Fin.forall_fin_succ]`"
    constructor <;> simp [IsRowEchelon, IsLeadingEntry, Fin.forall_fin_succ]
  · Hint "Record your row operations: express each row of $R$ as a combination of the
    original rows $\\rho_1, \\rho_2, \\rho_3$. Those coefficients are the rows of $E$; $F$
    expresses each original row in terms of the rows of $R$ (or of $E A$)."
    Hint (hidden := true) "Row 1 of $R$ is $-\\rho_3$, row 2 is $\\frac13(\\rho_1 + \\rho_3)$, row 3
    is $\\rho_2 - 2\\rho_1$:
    `use !![0, 0, -1; 1/3, 0, 1/3; -2, 1, 0], !![1, 3, 0; 2, 6, 1; -1, 0, 0]`"
    use !![0, 0, -1; 1/3, 0, 1/3; -2, 1, 0], !![1, 3, 0; 2, 6, 1; -1, 0, 0]
    Hint (hidden := true) "`constructor`, then for each `entrywise <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]`."
    constructor
    · entrywise <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]
    · entrywise <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]

end LinearAlgebraGame

Conclusion "**Answer:** $\\begin{pmatrix}1&0&0\\\\0&1&1/3\\\\0&0&0\\end{pmatrix}$."

NewDefinition Matrix.IsReducedRowEchelon Matrix.IsRowEchelon
NewTheorem Matrix.IsLeadingEntry Fin.forall_fin_succ
