import Game.Levels.MatrixAlgebra.L02_TransposeProduct

World "MatrixAlgebra"
Level 3
Title "H Hᵀ is symmetric"

-- @sheet 7 Q7b
/-! @answer
By part (a), $(HH^{\mathsf T})^{\mathsf T} = (H^{\mathsf T})^{\mathsf T}H^{\mathsf T} = HH^{\mathsf T}$,
since transposing twice gives back $H$. Likewise
$(H^{\mathsf T}H)^{\mathsf T} = H^{\mathsf T}(H^{\mathsf T})^{\mathsf T} = H^{\mathsf T}H$.
Both are therefore equal to their own transposes, i.e. symmetric.
-/
Introduction "
**Problem Sheet 7, Question 7(b).** A square matrix is *symmetric* if each $i,j$ entry equals
the $j,i$ entry, that is, if the matrix equals its own transpose. Show that the matrices
$HH^{\\mathsf T}$ and $H^{\\mathsf T}H$ are symmetric.

Your `transpose_mul'` from the last level is in the inventory.
"

namespace LinearAlgebraGame

open Matrix in
/-- $HH^{\mathsf T}$ and $H^{\mathsf T}H$ equal their own transposes. -/
Statement {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) :
    (H * Hᵀ)ᵀ = H * Hᵀ ∧ (Hᵀ * H)ᵀ = Hᵀ * H := by
  constructor
  · Hint (hidden := true) "`rw [transpose_mul', Matrix.transpose_transpose]`"
    rw [transpose_mul', Matrix.transpose_transpose]
  · rw [transpose_mul', Matrix.transpose_transpose]

end LinearAlgebraGame

Conclusion "
Gram matrices $H^{\\mathsf T}H$ are always symmetric — you will meet them again in least squares.
"

NewTheorem Matrix.transpose_transpose
DisabledTactic simp norm_num
DisabledTheorem Matrix.transpose_mul
TheoremTab "Matrices"
