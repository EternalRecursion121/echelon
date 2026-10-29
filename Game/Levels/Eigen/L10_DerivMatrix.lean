import Game.Levels.Eigen.L09_Multiplicities

World "Eigen"
Level 10
Title "The matrix of d/dx"

Introduction "
The game models $\\mathcal P_3$ as `Poly 3`: a cubic $a_0 + a_1x + a_2x^2 + a_3x^3$ is its
coefficient vector $(a_0, a_1, a_2, a_3)$, i.e. coordinates with respect to
$\\langle 1, x, x^2, x^3\\rangle$. `Poly.deriv` is $d/dx$: the coefficient of $x^i$ in $p'$ is
$(i+1)a_{i+1}$.

**Prove** that with respect to this basis $d/dx$ is represented by
$$D = \\begin{pmatrix} 0&1&0&0\\\\ 0&0&2&0\\\\ 0&0&0&3\\\\ 0&0&0&0\\end{pmatrix}.$$
"

namespace LinearAlgebraGame

open Matrix in
/-- $\frac{d}{dx}p = Dp$ for every $p \in \mathcal P_3$. -/
Statement deriv_eq_mulVec (p : Poly 3) :
    Poly.deriv p = (!![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ p := by
  Hint "Compare the four coordinates."
  Hint (hidden := true) "`entrywise`, and in each case
  `simp [Poly.deriv, Matrix.mulVec, dotProduct, Fin.sum_univ_four]`, then `norm_num` for what is left."
  entrywise <;> simp [Poly.deriv, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

end LinearAlgebraGame

Conclusion "Column $j$ of $D$ is the derivative of the $j$-th basis vector: $(x^j)' = jx^{j-1}$."

NewDefinition LinearAlgebraGame.Poly.deriv

TheoremTab "Eigen"
