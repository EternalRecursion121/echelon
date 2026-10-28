import Game.Levels.MatrixAlgebra.L07_InverseTranspose

World "MatrixAlgebra"
Level 8
Title "Inverse of a symmetric matrix"

-- @sheet 7 Q7d
/-! @answer
Let $A$ be symmetric and invertible. By part (c),
$(A^{-1})^{\mathsf T} = (A^{\mathsf T})^{-1} = A^{-1}$, so $A^{-1}$ is symmetric.
-/
Introduction "
**Problem Sheet 7, Question 7(d).** Show that the inverse of a symmetric matrix is symmetric.
"

namespace LinearAlgebraGame

open Matrix in
/-- If $A^{\mathsf T} = A$ is invertible then $(A^{-1})^{\mathsf T} = A^{-1}$. -/
Statement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (hs : Aᵀ = A) :
    (A⁻¹)ᵀ = A⁻¹ := by
  Hint "Part (c) does almost everything."
  Hint (hidden := true) "`rw [← inv_transpose' A hA, hs]`"
  rw [← inv_transpose' A hA, hs]

end LinearAlgebraGame

Conclusion "
Symmetric in, symmetric out.
"

DisabledTheorem Matrix.transpose_nonsing_inv
DisabledTactic simp norm_num
TheoremTab "Matrices"
