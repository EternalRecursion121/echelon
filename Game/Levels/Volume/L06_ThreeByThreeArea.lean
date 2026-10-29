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

The natural candidate is the determinant with a row of ones on top of the coordinates,
$\\begin{vmatrix} 1&1&1\\\\ x_1&x_2&x_3\\\\ y_1&y_2&y_3\\end{vmatrix}$. **Find the constant** $c$ with
$\\triangle ABC = c\\cdot$ (that determinant) for all triangles (signed area).
"

namespace LinearAlgebraGame

/-- There is a constant $c$ with $\triangle ABC = c \begin{vmatrix} 1&1&1\\ x_1&x_2&x_3\\ y_1&y_2&y_3\end{vmatrix}$ for all $A, B, C$. -/
Statement : ∃ c : ℝ, ∀ x₁ y₁ x₂ y₂ x₃ y₃ : ℝ,
    triArea ![x₁, y₁] ![x₂, y₂] ![x₃, y₃]
      = c * (!![1, 1, 1; x₁, x₂, x₃; y₁, y₂, y₃] : Matrix (Fin 3) (Fin 3) ℝ).det := by
  Hint "Expand both determinants and compare: which constant makes them agree?"
  Hint (hidden := true) "`use 1 / 2`, `intro x₁ y₁ x₂ y₂ x₃ y₃`, then `unfold triArea`,
  `rw [Matrix.det_fin_two_of, Matrix.det_fin_three]`, `simp`, `ring`."
  use 1 / 2
  intro x₁ y₁ x₂ y₂ x₃ y₃
  unfold triArea
  rw [Matrix.det_fin_two_of, Matrix.det_fin_three]
  simp
  ring

end LinearAlgebraGame

Conclusion "$c = \\tfrac12$. Expanding along the first row of the $3\\times3$ determinant gives back the three $2\\times2$ determinants of part (b)."

TheoremTab "Det"
