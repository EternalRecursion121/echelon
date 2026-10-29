import Game.Levels.MatrixAlgebra.L05_ZeroProduct

World "MatrixAlgebra"
Level 6
Title "Inverse of a power"

-- @sheet 7 Q5
/-! @answer
**Yes.** It suffices to show $(T^{-1})^k\,T^k = I$, since then $(T^{-1})^k$ is a (left, hence
two-sided) inverse of $T^k$. By induction on $k$: for $k = 0$ both are $I$. For $k+1$,
$(T^{-1})^{k+1}T^{k+1} = (T^{-1})^k(T^{-1}T)T^k = (T^{-1})^kT^k = I$ by the induction hypothesis.
Hence $(T^k)^{-1} = (T^{-1})^k$.
-/
Introduction "
**Problem Sheet 7, Question 5.** Let $T$ be a nonsingular matrix. Is $(T^k)^{-1} = (T^{-1})^k$?

Decide (`left`: no, `right`: yes), then prove.

\"$T$ nonsingular\" is `hT : IsUnit T.det` here (see the world introduction):
it is what Mathlib needs before `T⁻¹` really is an inverse.
"

namespace LinearAlgebraGame

/-- For nonsingular $T$, is $(T^k)^{-1} = (T^{-1})^k$ for every $k$? -/
Statement {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det) :
    (¬ ∀ k : ℕ, (T ^ k)⁻¹ = (T⁻¹) ^ k) ∨ (∀ k : ℕ, (T ^ k)⁻¹ = (T⁻¹) ^ k) := by
  Hint "Decide first: test small cases, e.g. $k = 2$. Multiply $(T^\{-1})^2$ by $T^2$ and see
  what you get."
  Hint (hidden := true) "$(T^\{-1})^2 T^2 = T^\{-1}(T^\{-1}T)T$. The middle cancels."
  right
  Hint "Tools: `Matrix.inv_eq_left_inv : B * A = 1 → A⁻¹ = B` turns the claim into a product
  equal to $I$, and `Matrix.nonsing_inv_mul T hT : T⁻¹ * T = 1` cancels."
  intro k
  Hint (hidden := true) "`apply Matrix.inv_eq_left_inv`, then `induction k with` …"
  apply Matrix.inv_eq_left_inv
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one]
  | succ k ih =>
    Hint (hidden := true) "Regroup as $(T^\{-1})^k (T^\{-1}T) T^k$ with `pow_succ`, `pow_succ'`
    and `Matrix.mul_assoc`, then cancel the middle."
    calc T⁻¹ ^ (k + 1) * T ^ (k + 1) = T⁻¹ ^ k * (T⁻¹ * T) * T ^ k := by
          rw [pow_succ, pow_succ', Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul T hT, Matrix.mul_one, ih]

end LinearAlgebraGame

Conclusion "
**Yes**: $(T^k)^{-1} = (T^{-1})^k$, so $T^{-k}$ is unambiguous.
"

DisabledTheorem Matrix.inv_pow' inv_pow Matrix.inv_zpow
DisabledTactic simp norm_num
TheoremTab "Matrices"
NewTheorem Matrix.inv_eq_left_inv pow_succ' pow_succ pow_zero Matrix.nonsing_inv_mul Matrix.mul_nonsing_inv
NewDefinition IsUnit
