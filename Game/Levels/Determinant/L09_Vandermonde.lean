import Game.Levels.Determinant.L08_ThreeByThree

World "Determinant"
Level 9
Title "Vandermonde"

-- @sheet 8 Q7
/-! @answer
Subtract column 1 from columns 2 and 3:
$$\begin{vmatrix} 1&1&1\\ x_1&x_2&x_3\\ x_1^2&x_2^2&x_3^2\end{vmatrix}
= \begin{vmatrix} 1&0&0\\ x_1&x_2-x_1&x_3-x_1\\ x_1^2&x_2^2-x_1^2&x_3^2-x_1^2\end{vmatrix}
= (x_2-x_1)(x_3^2-x_1^2) - (x_3-x_1)(x_2^2-x_1^2).$$
Factor out $(x_2-x_1)(x_3-x_1)$: what remains is $(x_3+x_1) - (x_2+x_1) = x_3 - x_2$.
So the determinant is $(x_2-x_1)(x_3-x_1)(x_3-x_2)$, the product of $x_j - x_i$ over $i<j$.
-/
Introduction "
**Problem Sheet 8, Question 7.** The determinant of the transpose of the Vandermonde
matrix,
$$\\begin{vmatrix} 1&1&\\cdots&1\\\\ x_1&x_2&\\cdots&x_n\\\\ \\vdots&&&\\vdots\\\\ x_1^{n-1}&x_2^{n-1}&\\cdots&x_n^{n-1}\\end{vmatrix},$$
equals the product over all $i < j$ of $x_j - x_i$. Prove this for $n = 3$.
"

namespace LinearAlgebraGame

/-- $\begin{vmatrix} 1&1&1\\ x_1&x_2&x_3\\ x_1^2&x_2^2&x_3^2\end{vmatrix} = (x_2-x_1)(x_3-x_1)(x_3-x_2)$. -/
Statement (x₁ x₂ x₃ : ℝ) :
    (!![1, 1, 1; x₁, x₂, x₃; x₁ ^ 2, x₂ ^ 2, x₃ ^ 2] : Matrix (Fin 3) (Fin 3) ℝ).det
      = (x₂ - x₁) * (x₃ - x₁) * (x₃ - x₂) := by
  Hint "Expand the determinant; both sides are then polynomials in $x_1, x_2, x_3$."
  Hint (hidden := true) "`rw [Matrix.det_fin_three]`, `simp`, then `ring`."
  rw [Matrix.det_fin_three]
  simp
  ring

end LinearAlgebraGame

Conclusion "
In your write-up, show the column operations: subtract column 1 from columns 2 and 3, then
factor. The product is nonzero exactly when the $x_i$ are distinct, which is why there is a
unique interpolating polynomial through $n$ points with distinct $x$-coordinates.
"

DisabledTheorem Matrix.det_vandermonde
TheoremTab "Det"
