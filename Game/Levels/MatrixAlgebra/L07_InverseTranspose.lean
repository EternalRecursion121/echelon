import Game.Levels.MatrixAlgebra.L06_InversePower

World "MatrixAlgebra"
Level 7
Title "Inverse of the transpose"

-- @sheet 7 Q7c
/-! @answer
Let $T$ be invertible. By part (a), $(T^{-1})^{\mathsf T}\,T^{\mathsf T} = (T\,T^{-1})^{\mathsf T}
= I^{\mathsf T} = I$, so $(T^{-1})^{\mathsf T}$ is an inverse of $T^{\mathsf T}$:
$(T^{\mathsf T})^{-1} = (T^{-1})^{\mathsf T}$. In particular $T^{\mathsf T}$ is invertible.
-/
Introduction "
**Problem Sheet 7, Question 7(c).** Show that the inverse of the transpose is the transpose of
the inverse.
"

namespace LinearAlgebraGame

open Matrix in
/-- For invertible $T$: $(T^{\mathsf T})^{-1} = (T^{-1})^{\mathsf T}$. -/
Statement inv_transpose' {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det) :
    (Tᵀ)⁻¹ = (T⁻¹)ᵀ := by
  Hint "Show that $(T^\{-1})^\{\\mathsf T}$ times $T^\{\\mathsf T}$ is $I$, using part (a) backwards."
  apply Matrix.inv_eq_left_inv
  Hint (hidden := true) "`rw [← transpose_mul', Matrix.mul_nonsing_inv T hT, Matrix.transpose_one]`"
  rw [← transpose_mul', Matrix.mul_nonsing_inv T hT, Matrix.transpose_one]

end LinearAlgebraGame

Conclusion "
Transposing and inverting commute.
"

DisabledTheorem Matrix.transpose_nonsing_inv Matrix.transpose_mul
DisabledTactic simp norm_num
TheoremTab "Matrices"
NewTheorem Matrix.transpose_one
