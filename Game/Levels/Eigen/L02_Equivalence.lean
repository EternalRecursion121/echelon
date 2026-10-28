import Game.Levels.Eigen.L01_SimilarZero

World "Eigen"
Level 2
Title "An equivalence relation"

-- @sheet 9 Q5
/-! @answer
*Reflexive:* $T = ITI^{-1}$. *Symmetric:* if $\hat T = PTP^{-1}$ then
$T = P^{-1}\hat T P = P^{-1}\hat T (P^{-1})^{-1}$, and $P^{-1}$ is nonsingular.
*Transitive:* if $\hat T = PTP^{-1}$ and $\tilde T = Q\hat T Q^{-1}$ then
$\tilde T = QPTP^{-1}Q^{-1} = (QP)T(QP)^{-1}$, and $QP$ is nonsingular.
-/
Introduction "
**Problem Sheet 9, Question 5.** Show that similarity is an equivalence relation, starting
from the definition that $\\hat T$ is similar to $T$ if $\\hat T = PTP^{-1}$.

`constructor` splits `Equivalence MatSimilar` into reflexivity, symmetry and transitivity.
Useful facts about a nonsingular $P$ (`hP : IsUnit P`): `mul_inv_of_isUnit hP`,
`inv_mul_of_isUnit hP`, `isUnit_inv_of_isUnit hP`, `inv_inv_of_isUnit hP`, and
`Matrix.mul_inv_rev : (A * B)⁻¹ = B⁻¹ * A⁻¹`.
"

namespace LinearAlgebraGame

/-- Similarity of $n\times n$ matrices is an equivalence relation. -/
Statement {n : ℕ} : Equivalence (@MatSimilar n) := by
  Hint "Reflexive: $P = I$. Symmetric: use $P⁻¹$. Transitive: use $QP$."
  constructor
  · intro T
    Hint (hidden := true) "`use 1`, then `constructor`: `isUnit_one`, and
    `rw [Matrix.one_mul, inv_one, Matrix.mul_one]`."
    use 1
    constructor
    · exact isUnit_one
    · rw [Matrix.one_mul, inv_one, Matrix.mul_one]
  · intro T S h
    obtain ⟨P, hP, hS⟩ := h
    Hint (hidden := true) "`use P⁻¹`. For the equation, `rw [hS, inv_inv_of_isUnit hP]` and
    regroup with `Matrix.mul_assoc` until `P⁻¹ * P` and `P * P⁻¹` appear side by side."
    use P⁻¹
    constructor
    · exact isUnit_inv_of_isUnit hP
    · rw [hS, inv_inv_of_isUnit hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_of_isUnit hP,
        Matrix.one_mul, Matrix.mul_assoc, inv_mul_of_isUnit hP, Matrix.mul_one]
  · intro T S U h1 h2
    obtain ⟨P, hP, hS⟩ := h1
    obtain ⟨Q, hQ, hU⟩ := h2
    Hint (hidden := true) "`use Q * P`; nonsingular by `IsUnit.mul hQ hP`; then
    `rw [hU, hS, Matrix.mul_inv_rev]` and `simp only [Matrix.mul_assoc]`."
    use Q * P
    constructor
    · exact IsUnit.mul hQ hP
    · rw [hU, hS, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]

end LinearAlgebraGame

Conclusion "So the square matrices split into similarity classes."

NewDefinition Equivalence
TheoremTab "Eigen"
NewTheorem Matrix.mul_inv_rev inv_one isUnit_one IsUnit.mul LinearAlgebraGame.inv_inv_of_isUnit LinearAlgebraGame.inv_mul_of_isUnit LinearAlgebraGame.isUnit_inv_of_isUnit
