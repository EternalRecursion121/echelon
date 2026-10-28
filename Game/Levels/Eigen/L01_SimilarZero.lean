import Game.Metadata
import Game.Ch45

World "Eigen"
Level 1
Title "Similar to zero"

Introduction "
**Definition Five.II.1.2.** $\\hat T$ is *similar* to $T$ if $\\hat T = PTP^{-1}$ for some
nonsingular $P$. In Lean: `MatSimilar T S` means `∃ P, IsUnit P ∧ S = P * T * P⁻¹`.
(Mathlib's name `Similar` is taken by geometry.)

Similar matrices represent the same transformation with respect to different bases.
**Example 1.4:** the only matrix similar to the zero matrix is the zero matrix itself.
"

namespace LinearAlgebraGame

/-- If $S$ is similar to the zero matrix then $S = 0$. -/
Statement {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (h : MatSimilar 0 S) : S = 0 := by
  Hint "Unpack the definition: $S = P\\,0\\,P⁻¹$."
  Hint (hidden := true) "`obtain ⟨P, hP, hS⟩ := h`."
  obtain ⟨P, hP, hS⟩ := h
  Hint (hidden := true) "`rw [hS, Matrix.mul_zero, Matrix.zero_mul]`."
  rw [hS, Matrix.mul_zero, Matrix.zero_mul]

end LinearAlgebraGame

Conclusion "Likewise only $I$ is similar to $I$: $PIP^{-1} = I$. Similarity classes can be very small."

NewDefinition LinearAlgebraGame.MatSimilar

TheoremTab "Eigen"
NewTheorem Matrix.zero_mul
