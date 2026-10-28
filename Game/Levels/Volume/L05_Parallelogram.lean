import Game.Levels.Volume.L04_TriangleSum

World "Volume"
Level 5
Title "Two by two determinants"

-- @sheet 10 Q1b
/-! @answer
$\triangle OAB$ is half of the parallelogram spanned by $\vec{OA}$ and $\vec{OB}$, which is
the image of the unit square under the matrix with columns $A$, $B$. So
$$\triangle OAB = \tfrac12\begin{vmatrix} x_1 & x_2\\ y_1 & y_2\end{vmatrix},\quad
\triangle OBC = \tfrac12\begin{vmatrix} x_2 & x_3\\ y_2 & y_3\end{vmatrix},\quad
\triangle OCA = \tfrac12\begin{vmatrix} x_3 & x_1\\ y_3 & y_1\end{vmatrix}$$
as signed areas (absolute values give the unsigned areas).
-/
Introduction "
**Problem Sheet 10, Question 1(b).** Express the three summands $\\triangle OAB$,
$\\triangle OBC$, $\\triangle OCA$ in terms of $2 \\times 2$ determinants.

By definition `triArea 0 A B` $= \\tfrac12\\begin{vmatrix} x_1 & x_2 \\\\ y_1 & y_2\\end{vmatrix}$.
Prove that this really is (up to sign) half the area of the parallelogram on $\\vec{OA}$,
$\\vec{OB}$: that parallelogram is the image of the unit square $[0,1]^2$ under the matrix
whose columns are $A$ and $B$.
"

namespace LinearAlgebraGame

open MeasureTheory in
/-- The parallelogram on $\vec{OA}, \vec{OB}$ has area $2\,|\triangle OAB|$, where $\triangle OAB = \frac12\begin{vmatrix} x_1 & x_2 \\ y_1 & y_2\end{vmatrix}$. -/
Statement (A B : Fin 2 → ℝ) :
    (volume (Matrix.toLin' !![A 0, B 0; A 1, B 1] '' Set.Icc 0 1)).toReal
      = 2 * |triArea 0 A B| := by
  Hint "Area of the image $= |\\det| \\cdot$ area of the unit square $= |\\det|$."
  Hint (hidden := true) "`rw [volume_image_matrix, Real.volume_Icc_pi_toReal zero_le_one]`."
  rw [volume_image_matrix, Real.volume_Icc_pi_toReal zero_le_one]
  Hint (hidden := true) "`unfold triArea`, `rw [Matrix.det_fin_two_of, Matrix.det_fin_two_of]`,
  `norm_num [abs_mul]`, and `ring` for what is left."
  unfold triArea
  rw [Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  norm_num [abs_mul]
  ring

end LinearAlgebraGame

Conclusion "
So $\\triangle OAB = \\tfrac12\\begin{vmatrix} x_1 & x_2 \\\\ y_1 & y_2\\end{vmatrix}$,
$\\triangle OBC = \\tfrac12\\begin{vmatrix} x_2 & x_3 \\\\ y_2 & y_3\\end{vmatrix}$,
$\\triangle OCA = \\tfrac12\\begin{vmatrix} x_3 & x_1 \\\\ y_3 & y_1\\end{vmatrix}$ (signed).
"

NewTheorem zero_le_one abs_mul
DisabledTactic simp
TheoremTab "Det"
