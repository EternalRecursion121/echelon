import Game.Levels.Diagonalisation.L08_Factored

World "Diagonalisation"
Level 9
Title "Determinant = product of eigenvalues"

-- @sheet 10 Q8c
/-! @answer
Put $x = 0$ in (b): $p(0) = |A - 0I| = |A|$, and also
$p(0) = (\lambda_1 - 0)\cdots(\lambda_n - 0) = \lambda_1\cdots\lambda_n$. So
$\det A = \lambda_1\lambda_2\cdots\lambda_n$.
-/
Introduction "
**Problem Sheet 10, Question 8(c).** Consider $p(0)$ to show that the determinant of a
matrix is the product of its eigenvalues.

(Same formulation as part (b): the eigenvalues are given by the factorisation `h`.)
"

namespace LinearAlgebraGame

open Polynomial in
/-- If $\det(xI - A) = \prod_i (x - \lambda_i)$ then $\det A = \prod_i \lambda_i$. -/
Statement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ)
    (h : A.charpoly = ∏ i, (X - C (l i))) : A.det = ∏ i, l i := by
  Hint "Evaluate both sides of part (b) at $x = 0$."
  Hint (hidden := true) "`have h2 := congrArg (eval 0) (charpolyH_eq_prod A l h)`, then
  `rw [charpolyH_eval, zero_smul, sub_zero, eval_prod] at h2`."
  have h2 := congrArg (eval 0) (charpolyH_eq_prod A l h)
  rw [charpolyH_eval, zero_smul, sub_zero, eval_prod] at h2
  rw [h2]
  Hint (hidden := true) "`apply Finset.prod_congr rfl`, `intro i _`, `rw [eval_sub, eval_C, eval_X, sub_zero]`."
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_sub, eval_C, eval_X, sub_zero]

end LinearAlgebraGame

Conclusion "$\\det A = \\lambda_1\\cdots\\lambda_n$. In particular $A$ is singular iff $0$ is an eigenvalue."

NewTheorem LinearAlgebraGame.charpolyH_eq_prod Polynomial.eval_prod Polynomial.eval_sub Polynomial.eval_C Polynomial.eval_X Finset.prod_congr
DisabledTheorem Matrix.det_eq_prod_roots_charpoly Matrix.det_eq_prod_roots_charpoly_of_splits
TheoremTab "Eigen"
