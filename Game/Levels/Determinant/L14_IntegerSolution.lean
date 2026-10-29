import Game.Levels.Determinant.L13_AdjDiagonal

World "Determinant"
Level 14
Title "Integer solutions"

-- @sheet 9 Q3
/-! @answer
Write the system as $A\vec x = \vec b$ with $A$ an $n\times n$ integer matrix, $\vec b$ an
integer vector and $\det A = -1$. Since $\det A \ne 0$ the system has a unique solution,
$\vec x = A^{-1}\vec b$. By the adjoint formula $A\,\operatorname{adj}(A) = \det(A) I = -I$, so
$A^{-1} = -\operatorname{adj}(A)$. The entries of $\operatorname{adj}(A)$ are cofactors,
i.e. $\pm$ determinants of integer matrices, hence integers. So
$\vec x = -\operatorname{adj}(A)\,\vec b$ has integer entries.
-/
Introduction "
**Problem Sheet 9, Question 3.** Suppose that a linear system has as many equations as
unknowns, that all of its coefficients and constants are integers, and that its matrix of
coefficients has determinant $-1$. Prove that the entries in the solution are all integers.

*Formulation.* We work over $\\mathbb Z$ and prove that the system $A\\vec x = \\vec b$ **has a
solution with integer entries**. Since $\\det A \\ne 0$ the solution over $\\mathbb Q$ or
$\\mathbb R$ is unique (Lemma Four.I.2.4), so this integer solution *is* the solution.

The adjoint satisfies `Matrix.mul_adjugate : A * adjugate A = A.det • 1`, over any
commutative ring — in particular over $\\mathbb Z$.
"

namespace LinearAlgebraGame

open Matrix in
/-- If an integer matrix $A$ has $\det A = -1$, then $A\vec x = \vec b$ has an integer solution for every integer $\vec b$. -/
Statement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det = -1) (b : Fin n → ℤ) :
    ∃ x : Fin n → ℤ, A *ᵥ x = b := by
  Hint "Idea: what is $A^\{-1}$ when $\\det A = -1$? Are its entries integers?"
  Hint (hidden := true) "The inverse of A is adj(A)/det A = −adj(A), whose entries are integers.
  So try x = −adj(A) b."
  Hint (hidden := true) "`use -(adjugate A *ᵥ b)`."
  use -(adjugate A *ᵥ b)
  Hint (hidden := true) "`rw [mulVec_neg, mulVec_mulVec, mul_adjugate, hA]`, then tidy up with
  `neg_smul, one_smul, neg_mulVec, one_mulVec, neg_neg`."
  rw [mulVec_neg, mulVec_mulVec, mul_adjugate, hA, neg_smul, one_smul, neg_mulVec, one_mulVec,
    neg_neg]

end LinearAlgebraGame

Conclusion "This is Cramer's rule in disguise: each $x_i$ is a ratio of integer determinants with denominator $\\pm1$."

NewTheorem Matrix.mulVec_neg Matrix.mul_adjugate neg_smul Matrix.neg_mulVec
TheoremTab "Det"
