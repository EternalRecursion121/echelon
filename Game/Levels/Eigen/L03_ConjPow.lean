import Game.Levels.Eigen.L02_Equivalence

World "Eigen"
Level 3
Title "Powers of a similar matrix"

Introduction "
If $\\hat T = PTP^{-1}$ then $\\hat T^2 = PTP^{-1}PTP^{-1} = PT^2P^{-1}$: the inner
$P^{-1}P$ cancels. **Prove** $(PTP^{-1})^k = PT^kP^{-1}$ for all $k$, by induction.
"

namespace LinearAlgebraGame

/-- $(PTP^{-1})^k = PT^kP^{-1}$ for nonsingular $P$. -/
Statement conj_pow_eq {n : ℕ} (P T : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P) (k : ℕ) :
    (P * T * P⁻¹) ^ k = P * T ^ k * P⁻¹ := by
  Hint "Induction on $k$. For $k+1$, write $\\hat T^(k+1) = \\hat T^k \\hat T$ and cancel $P⁻¹P$."
  Hint (hidden := true) "`induction k with` and cases `| zero => …` and `| succ k ih => …`."
  induction k with
  | zero =>
    Hint (hidden := true) "`rw [pow_zero, pow_zero, Matrix.mul_one, mul_inv_of_isUnit hP]`."
    rw [pow_zero, pow_zero, Matrix.mul_one, mul_inv_of_isUnit hP]
  | succ k ih =>
    Hint (hidden := true) "`rw [pow_succ, ih, pow_succ]`, then
    `calc` or a careful `rw` with `Matrix.mul_assoc` to bring `P⁻¹ * P` together."
    rw [pow_succ, ih, pow_succ]
    calc P * T ^ k * P⁻¹ * (P * T * P⁻¹) = P * T ^ k * (P⁻¹ * P) * T * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = P * (T ^ k * T) * P⁻¹ := by
          rw [inv_mul_of_isUnit hP, Matrix.mul_one, Matrix.mul_assoc P]

end LinearAlgebraGame

Conclusion "Similar matrices have similar powers, with the same $P$."

DisabledTheorem conj_pow
TheoremTab "Eigen"
