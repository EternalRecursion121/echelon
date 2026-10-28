import Game.Levels.Determinant.L05_MathlibDet

World "Determinant"
Level 6
Title "Two by two"

Introduction "
For $2 \\times 2$ matrices, $\\begin{vmatrix} a & b \\\\ c & d \\end{vmatrix} = ad - bc$
(`Matrix.det_fin_two_of`). Compute the determinant of the matrix from Sheet 9 Q2.
"

namespace LinearAlgebraGame

/-- $\begin{vmatrix} 2 & 3 \\ 4 & -1 \end{vmatrix} = -14$. -/
Statement : (!![2, 3; 4, -1] : Matrix (Fin 2) (Fin 2) ℝ).det = -14 := by
  Hint "Expand with the $ad - bc$ formula, then do the arithmetic."
  Hint (hidden := true) "`rw [Matrix.det_fin_two_of]` then `ring`."
  rw [Matrix.det_fin_two_of]
  ring

end LinearAlgebraGame

Conclusion "$2 \\cdot (-1) - 3 \\cdot 4 = -14$."

NewTheorem Matrix.det_fin_two_of
DisabledTactic simp norm_num
TheoremTab "Det"
