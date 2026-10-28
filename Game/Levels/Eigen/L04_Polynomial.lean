import Game.Levels.Eigen.L03_ConjPow

World "Eigen"
Level 4
Title "Polynomials of similar matrices"

-- @sheet 9 Q6
/-! @answer
Let $S = PTP^{-1}$. By induction $S^k = PT^kP^{-1}$ (the inner $P^{-1}P$ cancel). Then
$$p(S) = \sum_k c_k S^k = \sum_k c_k PT^kP^{-1} = P\Big(\sum_k c_kT^k\Big)P^{-1} = P\,p(T)\,P^{-1}$$
(for $k = 0$, $S^0 = I = PIP^{-1}$), using that matrix multiplication distributes over sums
and commutes with scalars. So $p(T)$ is similar to $p(S)$ via the same $P$.
-/
Introduction "
**Problem Sheet 9, Question 6.** Let $p(x) = c_mx^m + \\cdots + c_1x + c_0$. Show that if
$T$ is similar to $S$ then $p(T) = c_mT^m + \\cdots + c_1T + c_0I$ is similar to
$p(S) = c_mS^m + \\cdots + c_1S + c_0I$.

In Lean, $p(T)$ is `∑ i ∈ Finset.range (m + 1), c i • T ^ i` (and $T^0 = I$).
"

namespace LinearAlgebraGame

/-- If $T$ is similar to $S$ then $p(T)$ is similar to $p(S)$. -/
Statement {n : ℕ} (T S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (c : ℕ → ℝ) (h : MatSimilar T S) :
    MatSimilar (∑ i ∈ Finset.range (m + 1), c i • T ^ i)
      (∑ i ∈ Finset.range (m + 1), c i • S ^ i) := by
  Hint "Use the same $P$. Push $P$ and $P⁻¹$ inside the sum, and compare term by term."
  obtain ⟨P, hP, hS⟩ := h
  use P
  constructor
  · exact hP
  Hint (hidden := true) "`rw [hS, Finset.mul_sum, Finset.sum_mul]`, then
  `apply Finset.sum_congr rfl` and `intro i _`."
  rw [hS, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  Hint (hidden := true) "`rw [conj_pow_eq P T hP, Matrix.mul_smul, Matrix.smul_mul]`."
  rw [conj_pow_eq P T hP, Matrix.mul_smul, Matrix.smul_mul]

end LinearAlgebraGame

Conclusion "In particular similar matrices satisfy the same polynomial equations."

TheoremTab "Eigen"
NewTheorem LinearAlgebraGame.conj_pow_eq Finset.sum_mul Matrix.mul_smul Matrix.smul_mul
