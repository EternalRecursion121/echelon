import Game.Levels.MatrixAlgebra.L01_UpperTriangular

World "MatrixAlgebra"
Level 2
Title "Transpose of a product"

-- @sheet 7 Q7a
/-! @answer
Compare entries. $((GH)^{\mathsf T})_{ij} = (GH)_{ji} = \sum_k g_{jk}h_{ki}$, while
$(H^{\mathsf T}G^{\mathsf T})_{ij} = \sum_k (H^{\mathsf T})_{ik}(G^{\mathsf T})_{kj} = \sum_k h_{ki}g_{jk}$.
The sums agree term by term since real multiplication commutes, so $(GH)^{\mathsf T} = H^{\mathsf T}G^{\mathsf T}$.
-/
Introduction "
**Problem Sheet 7, Question 7(a).** Show that $(GH)^{\\mathsf T} = H^{\\mathsf T} G^{\\mathsf T}$.

Work entrywise: `Matrix.transpose_apply` says $(A^{\\mathsf T})_{ij} = A_{ji}$. (`simp` is
off here: it knows this theorem.)
"

namespace LinearAlgebraGame

open Matrix in
/-- $(GH)^{\mathsf T} = H^{\mathsf T} G^{\mathsf T}$. -/
Statement transpose_mul' {m n p : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin p) ℝ) : (G * H)ᵀ = Hᵀ * Gᵀ := by
  Hint "Compare the $(i,j)$ entries."
  ext i j
  Hint (hidden := true) "`rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.mul_apply]`"
  rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.mul_apply]
  Hint "Both sides are sums over $k$; match them term by term."
  Hint (hidden := true) "`apply Finset.sum_congr rfl`, `intro k _`, then
  `rw [Matrix.transpose_apply, Matrix.transpose_apply, mul_comm]`."
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.transpose_apply, Matrix.transpose_apply, mul_comm]

end LinearAlgebraGame

Conclusion "
The order reverses — just like putting on socks and shoes, and taking them off again.
"

NewTheorem Matrix.transpose_apply
NewDefinition Matrix.transpose
DisabledTactic simp norm_num
DisabledTheorem Matrix.transpose_mul
TheoremTab "Matrices"
