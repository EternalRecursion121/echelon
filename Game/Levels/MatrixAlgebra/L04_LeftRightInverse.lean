import Game.Levels.MatrixAlgebra.L03_Symmetric

World "MatrixAlgebra"
Level 4
Title "Left and right inverses agree"

Introduction "
Hefferon Lemma Three.IV.4.2: if $G$ is a left inverse of $H$ ($GH = I$) and $G'$ is a right
inverse ($HG' = I$), then $G = G'$. The proof is one line of associativity:
$G = GI = G(HG') = (GH)G' = IG' = G'$.
"

namespace LinearAlgebraGame

/-- If $GH = I$ and $HG' = I$ then $G = G'$. -/
Statement inv_left_eq_inv_right {n : ℕ} {H G G' : Matrix (Fin n) (Fin n) ℝ}
    (hG : G * H = 1) (hG' : H * G' = 1) : G = G' := by
  Hint "Associativity: $G = GI = G(HG') = (GH)G' = G'$."
  Hint (hidden := true) "Write that chain as a `calc`."
  Hint (hidden := true) "Steps: `Matrix.mul_one`, `{hG'}`, `Matrix.mul_assoc`, then
  `{hG}` and `Matrix.one_mul`."
  calc G = G * 1 := by rw [Matrix.mul_one]
    _ = G * (H * G') := by rw [hG']
    _ = (G * H) * G' := by rw [Matrix.mul_assoc]
    _ = G' := by rw [hG, Matrix.one_mul]

end LinearAlgebraGame

Conclusion "
So an invertible matrix has exactly one inverse, $H^{-1}$.
"

DisabledTheorem left_inv_eq_right_inv inv_eq_of_mul_eq_one_left Matrix.inv_eq_left_inv Matrix.inv_eq_right_inv mul_eq_one_comm
TheoremTab "Matrices"
NewTheorem Matrix.mul_assoc Matrix.one_mul
