import Game.Levels.Independence.L02_ContainsZero

World "Independence"
Level 3
Title "Two polynomials"

-- @sheet 3 Q4a
/-! @answer
**Independent.** Suppose $c_1(-x^2) + c_2(1 + 4x^2) = 0$. Comparing constant terms gives
$c_2 = 0$; then comparing $x^2$ terms gives $-c_1 + 4c_2 = 0$, so $c_1 = 0$. Only the trivial
relation exists.
-/
Introduction "
**Problem Sheet 3, Question 4.** Which of these subsets of $\\mathcal{P}_3$ are linearly
dependent and which are independent?

**(a)** $\\{-x^2,\\ 1 + 4x^2\\}$

As in Hefferon, a polynomial $a_0 + a_1x + a_2x^2 + a_3x^3 \\in \\mathcal P_3$ is stored as its
coefficient vector `![a₀, a₁, a₂, a₃] : Poly 3`, so $-x^2$ is `![0, 0, -1, 0]`.
Two polynomials are equal exactly when their coefficient vectors are.

Decide: `left` for dependent, `right` for independent.
"

namespace LinearAlgebraGame

/-- Is $\{-x^2, 1 + 4x^2\}$ linearly independent in $\mathcal P_3$? -/
Statement : (¬ LinearIndependent ℝ ![(![0, 0, -1, 0] : Poly 3), ![1, 0, 4, 0]]) ∨
    LinearIndependent ℝ ![(![0, 0, -1, 0] : Poly 3), ![1, 0, 4, 0]] := by
  Hint "Suppose $a(-x^2) + b(1 + 4x^2) = 0$. Look at the constant term, then the $x^2$ term."
  right
  rw [LinearIndependent.pair_iff]
  intro a b h
  Hint (hidden := true) "`have h0 := congrFun {h} 0` reads off the constant coefficient
  (similarly `congrFun {h} 2`); `simp at h0 h2` computes them."
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp at h0 h2
  constructor
  · linarith
  · exact h0

end LinearAlgebraGame

Conclusion "**Answer: independent.**"

TheoremTab "Independence"
