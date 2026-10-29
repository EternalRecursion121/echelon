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

\"$H$ invertible\" is Hefferon's definition (Three.IV.4.1): there is a matrix $H'$ with
$H'H = I$ and $HH' = I$. In Lean that is the hypothesis
`hH : ∃ H', H' * H = 1 ∧ H * H' = 1`; take it apart with `obtain`.
"

namespace LinearAlgebraGame

/-- If $H$ is invertible and $HG = 0$ then $G = 0$. -/
Statement {n : ℕ} (H G : Matrix (Fin n) (Fin n) ℝ) (hH : ∃ H', H' * H = 1 ∧ H * H' = 1)
    (h : H * G = 0) : G = 0 := by
  Hint "Use that $H$ is invertible: what happens if you multiply $HG = 0$ on the left by
  something?"
  Hint (hidden := true) "`obtain ⟨H', hl, hr⟩ := hH`, then multiply both sides of $HG = 0$
  on the left by $H'$: $G = (H'H)G = H'(HG) = 0$."
  obtain ⟨H', hl, hr⟩ := hH
  Hint (hidden := true) "A `calc` chain, using `{hl}`, `Matrix.one_mul`, `Matrix.mul_assoc`, `Matrix.mul_zero`."
  calc G = (H' * H) * G := by rw [hl, Matrix.one_mul]
    _ = H' * (H * G) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero]

end LinearAlgebraGame

Conclusion "
Invertible matrices can be cancelled; that is exactly what fails for singular ones.
"

TheoremTab "Matrices"
