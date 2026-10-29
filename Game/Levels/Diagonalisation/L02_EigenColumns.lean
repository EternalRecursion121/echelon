import Game.Levels.Diagonalisation.L01_Nilpotent

World "Diagonalisation"
Level 2
Title "Eigenvectors as columns"

Introduction "
**Lemma Five.II.2.4.** $T$ is diagonalisable exactly when there is a basis of eigenvectors.
In matrices: put the basis vectors $\\vec\\beta_1, \\dots, \\vec\\beta_n$ as the columns of $Q$.
Column $j$ of $TQ$ is $T\\vec\\beta_j$ and column $j$ of $Q\\,\\mathrm{diag}(\\lambda_1,\\dots,\\lambda_n)$ is
$\\lambda_j\\vec\\beta_j$, so \"the columns of $Q$ are eigenvectors\" is the single matrix equation
$$TQ = Q\\,\\mathrm{diag}(\\lambda_1, \\dots, \\lambda_n),$$
and \"they form a basis\" says $Q$ is nonsingular.

**Prove** the direction we need: then $T$ is diagonalisable (with $P = Q^{-1}$).

Facts about diagonal matrices you may need now or later: `Matrix.diagonal_smul`
($\\mathrm{diag}(c\\,d) = c\\,\\mathrm{diag}(d)$) and the earlier `diagonal_mul_diagonal`.
"

namespace LinearAlgebraGame

open Matrix in
/-- If $Q$ is nonsingular and $TQ = Q\,\mathrm{diag}(d)$, then $T$ is diagonalisable. -/
Statement diagonalizable_of_mul_eq {n : ℕ} (T Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsUnit Q)
    (d : Fin n → ℝ) (h : T * Q = Q * diagonal d) : Diagonalizable T := by
  Hint "Take $P = Q⁻¹$: then $PTP⁻¹ = Q⁻¹TQ = Q⁻¹Q\\,\\mathrm\{diag}(d) = \\mathrm\{diag}(d)$."
  Hint (hidden := true) "`use d, Q⁻¹, isUnit_inv_of_isUnit hQ`."
  use d, Q⁻¹, isUnit_inv_of_isUnit hQ
  Hint (hidden := true) "`rw [inv_inv_of_isUnit hQ, Matrix.mul_assoc, h]`, then regroup with
  `← Matrix.mul_assoc` and cancel `Q⁻¹ * Q`."
  rw [inv_inv_of_isUnit hQ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, inv_mul_of_isUnit hQ,
    Matrix.one_mul]

end LinearAlgebraGame

Conclusion "
In particular a diagonal matrix is diagonalisable (take $Q = I$). Next: when do the
eigenvectors form a basis?
"

NewTheorem LinearAlgebraGame.not_diagonalizable_of_sq_eq_zero Matrix.diagonal_smul
TheoremTab "Eigen"
