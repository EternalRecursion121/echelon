import Game.Levels.Volume.L05_Parallelogram

World "Volume"
Level 6
Title "One three by three determinant"

-- @sheet 10 Q1c
/-! @answer
Adding the three $2\times 2$ determinants from (b),
$$\triangle ABC = \tfrac12\left(\begin{vmatrix} x_1&x_2\\ y_1&y_2\end{vmatrix} + \begin{vmatrix} x_2&x_3\\ y_2&y_3\end{vmatrix} + \begin{vmatrix} x_3&x_1\\ y_3&y_1\end{vmatrix}\right)
= \tfrac12\begin{vmatrix} 1&1&1\\ x_1&x_2&x_3\\ y_1&y_2&y_3\end{vmatrix},$$
since Laplace expansion of the $3\times3$ determinant along its first row gives exactly
those three $2\times2$ minors (with the signs absorbed by reordering columns).
-/
Introduction "
**Problem Sheet 10, Question 1(c).** Express $\\triangle ABC$ in terms of a $3\\times3$
determinant.

**Answer to prove:** $\\triangle ABC = \\tfrac12\\begin{vmatrix} 1&1&1\\\\ x_1&x_2&x_3\\\\ y_1&y_2&y_3\\end{vmatrix}$ (signed area).
"

namespace LinearAlgebraGame

/-- $\triangle ABC = \frac12 \begin{vmatrix} 1&1&1\\ x_1&x_2&x_3\\ y_1&y_2&y_3\end{vmatrix}$. -/
Statement triArea_eq_det (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) :
    triArea ![x₁, y₁] ![x₂, y₂] ![x₃, y₃]
      = (1 / 2) * (!![1, 1, 1; x₁, x₂, x₃; y₁, y₂, y₃] : Matrix (Fin 3) (Fin 3) ℝ).det := by
  Hint "Expand both determinants and compare."
  Hint (hidden := true) "`unfold triArea`, `rw [Matrix.det_fin_two_of, Matrix.det_fin_three]`, `simp`, `ring`."
  unfold triArea
  rw [Matrix.det_fin_two_of, Matrix.det_fin_three]
  simp
  ring

end LinearAlgebraGame

Conclusion "Expanding along the first row of the $3\\times3$ determinant gives back the three $2\\times2$ determinants of part (b)."

TheoremTab "Det"
