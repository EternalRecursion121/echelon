import Game.Levels.Diagonalisation.L03_DistinctEigenvalues

World "Diagonalisation"
Level 4
Title "Scalar multiples"

-- @sheet 10 Q2a
/-! @answer
**Yes.** If $t$ is diagonalisable there is a basis $\vec\beta_1,\dots,\vec\beta_n$ of
eigenvectors, $t(\vec\beta_i) = \lambda_i\vec\beta_i$. Then $(ct)(\vec\beta_i) = (c\lambda_i)\vec\beta_i$,
so the same basis diagonalises $ct$. In matrices: if $PTP^{-1} = D$ then $P(cT)P^{-1} = cD$,
which is diagonal.
-/
Introduction "
**Problem Sheet 10, Question 2** (first part). Assume that $t, s\\colon V \\to V$ are each
diagonalisable. Is $ct$ diagonalisable for all scalars $c$?

We work with matrices (the representations of $t$, $s$ with respect to a basis of $V$).
*Decide level:* commit with `left` (no) or `right` (yes), then prove it.
"

namespace LinearAlgebraGame

open Matrix in
/-- True or false: if $T$ is diagonalisable then so is $cT$, for every $c$. -/
Statement :
    (¬ ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) ℝ) (c : ℝ), Diagonalizable T → Diagonalizable (c • T)) ∨
      (∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) ℝ) (c : ℝ), Diagonalizable T → Diagonalizable (c • T)) := by
  Hint "Can you prove it in general, or is there a small counterexample? Decide, then commit."
  right
  Hint "If $PTP⁻¹ = D$, what is $P(cT)P⁻¹$?"
  intro n T c h
  obtain ⟨d, P, hP, hD⟩ := h
  Hint (hidden := true) "`use c • d, P, hP`, then `rw [Matrix.mul_smul, Matrix.smul_mul, ← hD, diagonal_smul]`."
  use c • d, P, hP
  rw [Matrix.mul_smul, Matrix.smul_mul, ← hD, diagonal_smul]

end LinearAlgebraGame

Conclusion "**Yes**: the same eigenbasis works, with eigenvalues $c\\lambda_i$."

NewTheorem LinearAlgebraGame.diagonalizable_of_two_eigenvalues
TheoremTab "Eigen"
