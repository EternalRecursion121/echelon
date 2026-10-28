import Game.Levels.Diagonalisation.L06_OddSize

World "Diagonalisation"
Level 7
Title "The leading coefficient"

-- @sheet 10 Q8a
/-! @answer
In the permutation expansion of $|A - xI|$ each term is a product of $n$ entries, one from
each row and column. An entry contains $x$ only if it is on the diagonal, so only the
identity permutation, contributing $(a_{11} - x)\cdots(a_{nn} - x)$, has degree $n$; every other
term has at most $n-2$ diagonal factors. Hence the coefficient of $x^n$ is $(-1)^n$.
-/
Introduction "
**Problem Sheet 10, Question 8(a).** Let $A$ be an $n\\times n$ matrix. Use the permutation
expansion to find the coefficient of $x^n$ in the characteristic polynomial $p(x) = |A - xI|$.

*Formulation.* Mathlib has already done the permutation-expansion bookkeeping for its
characteristic polynomial $\\det(xI - A)$ (`Matrix.charpoly`): it is *monic* of degree $n$
(`Matrix.charpoly_monic`, `Matrix.charpoly_natDegree_eq_dim`). Hefferon's version differs by
the sign $(-1)^n$ (`charpolyH_eq`). Explain the permutation-expansion argument in your write-up.

**Prove:** the coefficient of $x^n$ in $|A - xI|$ is $(-1)^n$.
"

namespace LinearAlgebraGame

open Polynomial in
/-- The coefficient of $x^n$ in $|A - xI|$ is $(-1)^n$. -/
Statement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : (charpolyH A).coeff n = (-1) ^ n := by
  Hint "$|A - xI| = (-1)^n \\det(xI - A)$, and $\\det(xI - A)$ is monic of degree $n$."
  Hint (hidden := true) "`rw [charpolyH_eq, show ((-1 : ℝ[X]) ^ n) = C ((-1) ^ n) by simp, coeff_C_mul]`."
  rw [charpolyH_eq, show ((-1 : ℝ[X]) ^ n) = C ((-1) ^ n) by simp, coeff_C_mul]
  Hint (hidden := true) "`have h := (Matrix.charpoly_monic A).coeff_natDegree`, then
  `rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h`."
  have h := (Matrix.charpoly_monic A).coeff_natDegree
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  rw [h, mul_one]

end LinearAlgebraGame

Conclusion "The coefficient is $(-1)^n$: only the identity permutation reaches degree $n$."

NewTheorem LinearAlgebraGame.charpolyH_eq Polynomial.coeff_C_mul Matrix.charpoly_monic Polynomial.Monic.coeff_natDegree Matrix.charpoly_natDegree_eq_dim
NewDefinition Matrix.charpoly
TheoremTab "Eigen"
