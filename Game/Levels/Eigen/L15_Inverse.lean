import Game.Levels.Eigen.L14_ColumnSums

World "Eigen"
Level 15
Title "Eigenvalues of the inverse"

-- @sheet 10 Q4
/-! @answer
Let $T\vec v = \lambda\vec v$ with $\vec v \ne \vec 0$. First $\lambda \ne 0$: otherwise
$T\vec v = \vec 0$ and $\vec v = T^{-1}T\vec v = \vec 0$. Applying $T^{-1}$ to $T\vec v = \lambda\vec v$
gives $\vec v = \lambda T^{-1}\vec v$, so $T^{-1}\vec v = \lambda^{-1}\vec v$: $1/\lambda$ is an
eigenvalue of $T^{-1}$ with the same eigenvector. Applying this to $T^{-1}$ (whose inverse is $T$)
shows every eigenvalue of $T^{-1}$ arises this way, so the eigenvalues of $T^{-1}$ are exactly
$1/\lambda_1, \dots, 1/\lambda_n$.
-/
Introduction "
**Problem Sheet 10, Question 4.** Prove that if $T$ is nonsingular and has eigenvalues
$\\lambda_1,\\dots,\\lambda_n$ then $T^{-1}$ has eigenvalues $1/\\lambda_1,\\dots,1/\\lambda_n$.

**Prove:** if $\\lambda$ is an eigenvalue of nonsingular $T$, then $\\lambda \\ne 0$ and
$\\lambda^{-1}$ is an eigenvalue of $T^{-1}$. (Applied to $T^{-1}$, whose inverse is $T$, this
gives the converse, so the eigenvalues correspond exactly.)
"

namespace LinearAlgebraGame

open Matrix in
/-- If $T$ is nonsingular and $\lambda$ is an eigenvalue of $T$, then $\lambda \ne 0$ and $\lambda^{-1}$ is an eigenvalue of $T^{-1}$. -/
Statement {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T) (μ : ℝ)
    (h : IsEigenvalue T μ) : μ ≠ 0 ∧ IsEigenvalue T⁻¹ μ⁻¹ := by
  Hint "Apply $T⁻¹$ to both sides of $T\\vec v = \\lambda\\vec v$."
  obtain ⟨v, hv, hTv⟩ := h
  Hint (hidden := true) "Key fact: `have key : v = μ • (T⁻¹ *ᵥ v)`. Prove it with
  `calc v = (T⁻¹ * T) *ᵥ v := …` then `mulVec_mulVec`, `hTv`, `mulVec_smul`."
  have key : v = μ • (T⁻¹ *ᵥ v) := by
    calc v = (T⁻¹ * T) *ᵥ v := by rw [inv_mul_of_isUnit hT, one_mulVec]
      _ = T⁻¹ *ᵥ (T *ᵥ v) := by rw [mulVec_mulVec]
      _ = μ • (T⁻¹ *ᵥ v) := by rw [hTv, mulVec_smul]
  have hμ : μ ≠ 0 := by
    Hint (hidden := true) "`intro h0`, then `rw [h0, zero_smul] at key` contradicts `hv`."
    intro h0
    rw [h0, zero_smul] at key
    exact hv key
  constructor
  · exact hμ
  · use v
    constructor
    · exact hv
    · Hint (hidden := true) "`nth_rw 2 [key]`, then `rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]`."
      nth_rw 2 [key]
      rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]

end LinearAlgebraGame

Conclusion "Same eigenvectors, reciprocal eigenvalues."

TheoremTab "Eigen"
