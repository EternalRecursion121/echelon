import Game.Levels.Determinant.L06_TwoByTwo

World "Determinant"
Level 7
Title "Three by three"

Introduction "
The $3 \\times 3$ formula is `Matrix.det_fin_three` (six terms, one per permutation).
Compute the determinant of Hefferon's matrix from Five.II,
$$T = \\begin{pmatrix} 0 & 5 & 7 \\\\ -2 & 7 & 7 \\\\ -1 & 1 & 4 \\end{pmatrix}.$$
"

namespace LinearAlgebraGame

/-- The determinant of $\begin{pmatrix} 0 & 5 & 7 \\ -2 & 7 & 7 \\ -1 & 1 & 4 \end{pmatrix}$ is $40$. -/
Statement : (!![0, 5, 7; -2, 7, 7; -1, 1, 4] : Matrix (Fin 3) (Fin 3) ℝ).det = 40 := by
  Hint "Expand with the $3\\times3$ formula; then the entries need evaluating and the
  arithmetic done."
  Hint (hidden := true) "`rw [Matrix.det_fin_three]`, then `simp` evaluates the entries, then `norm_num`."
  rw [Matrix.det_fin_three]
  simp
  norm_num

end LinearAlgebraGame

Conclusion "
$-5\\cdot(-8+7) + 7\\cdot(-2+7) = 5 + 35 = 40$. Nonzero, so $T$ is nonsingular.
"

TheoremTab "Det"
