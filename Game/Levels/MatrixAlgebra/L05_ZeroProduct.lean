import Game.Levels.MatrixAlgebra.L04_LeftRightInverse

World "MatrixAlgebra"
Level 5
Title "HG = 0 with H invertible"

-- @sheet 7 Q6
/-! @answer
Multiply $HG = Z$ on the left by $H^{-1}$:
$G = IG = (H^{-1}H)G = H^{-1}(HG) = H^{-1}Z = Z$.
-/
Introduction "
**Problem Sheet 7, Question 6.** Assume that $H$ is invertible and that $HG$ is the zero matrix.
Show that $G$ is a zero matrix.

Mathlib writes $H^{-1}$ as `H⁻¹`; \"$H$ invertible\" is `IsUnit H.det`, and then
`Matrix.nonsing_inv_mul H hH : H⁻¹ * H = 1`.
"

namespace LinearAlgebraGame

/-- If $H$ is invertible and $HG = 0$ then $G = 0$. -/
Statement {n : ℕ} (H G : Matrix (Fin n) (Fin n) ℝ) (hH : IsUnit H.det) (h : H * G = 0) :
    G = 0 := by
  Hint "Use that $H$ is invertible: what happens if you multiply $HG = 0$ on the left by
  something?"
  Hint (hidden := true) "Multiply both sides of $HG = 0$ on the left by $H^\{-1}$:
  $G = (H^\{-1}H)G = H^\{-1}(HG) = 0$."
  Hint (hidden := true) "A `calc` chain, using `Matrix.nonsing_inv_mul H hH`, `Matrix.one_mul`, `Matrix.mul_assoc`, `Matrix.mul_zero`."
  calc G = (H⁻¹ * H) * G := by rw [Matrix.nonsing_inv_mul H hH, Matrix.one_mul]
    _ = H⁻¹ * (H * G) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero]

end LinearAlgebraGame

Conclusion "
Invertible matrices can be cancelled; that is exactly what fails for singular ones.
"

NewTheorem Matrix.nonsing_inv_mul Matrix.mul_nonsing_inv
TheoremTab "Matrices"
NewDefinition IsUnit
