import Game.Levels.Volume.L01_DetMul

World "Volume"
Level 2
Title "The inverse"

Introduction "
**Corollary Four.II.1.7:** if $T$ is nonsingular then $|T^{-1}| = 1/|T|$.

`IsUnit T` says $T$ is nonsingular (invertible); `mul_inv_of_isUnit hT : T * T⁻¹ = 1`.
"

namespace LinearAlgebraGame

/-- If $T$ is nonsingular then $\det(T^{-1}) = 1/\det T$. -/
Statement det_inv_eq {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T) :
    T⁻¹.det = 1 / T.det := by
  Hint "Idea: take determinants of both sides of T T⁻¹ = I."
  Hint (hidden := true) "`have h := congrArg Matrix.det (mul_inv_of_isUnit hT)`, then
  `rw [Matrix.det_mul, Matrix.det_one] at h`."
  have h := congrArg Matrix.det (mul_inv_of_isUnit hT)
  rw [Matrix.det_mul, Matrix.det_one] at h
  Hint (hidden := true) "You need $\\det T \\ne 0$ to divide: `left_ne_zero_of_mul_eq_one {h}`."
  have hd : T.det ≠ 0 := left_ne_zero_of_mul_eq_one h
  Hint (hidden := true) "`rw [eq_div_iff hd, mul_comm]` and `exact h`."
  rw [eq_div_iff hd, mul_comm]
  exact h

end LinearAlgebraGame

Conclusion "Geometrically: $T^{-1}$ undoes the volume scaling of $T$."

NewTheorem LinearAlgebraGame.mul_inv_of_isUnit left_ne_zero_of_mul_eq_one

DisabledTheorem Matrix.det_nonsing_inv
DisabledTactic simp norm_num field_simp
TheoremTab "Det"
