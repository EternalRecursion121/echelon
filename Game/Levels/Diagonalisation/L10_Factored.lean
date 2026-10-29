import Game.Levels.Diagonalisation.L09_LeadingCoeff

World "Diagonalisation"
Level 10
Title "In terms of the eigenvalues"

-- @sheet 10 Q8b
/-! @answer
Over $\mathbb C$ the characteristic polynomial factors completely, and its roots, listed with
multiplicity, are the eigenvalues $\lambda_1,\dots,\lambda_n$. By (a) its leading coefficient
is $(-1)^n$, so
$$p(x) = (-1)^n(x - \lambda_1)\cdots(x - \lambda_n) = (\lambda_1 - x)\cdots(\lambda_n - x).$$
-/
Introduction "
**Problem Sheet 10, Question 8(b).** Express $p(x) = |A - xI|$ in terms of the
eigenvalues $\\lambda_1,\\dots,\\lambda_n$ (some of which may be equal).

*Formulation.* \"$A$ has eigenvalues $\\lambda_1, \\dots, \\lambda_n$ (with multiplicity)\" means
that the monic characteristic polynomial factors as $\\det(xI - A) = \\prod_i (x - \\lambda_i)$.
Over $\\mathbb C$ this always happens; we stay over $\\mathbb R$ and take the factorisation as
the hypothesis `h`. `Finset.prod_neg` pulls the signs out of a product.

**Prove:** $p(x) = (\\lambda_1 - x)\\cdots(\\lambda_n - x)$.
"

namespace LinearAlgebraGame

open Polynomial in
/-- If $\det(xI - A) = \prod_i (x - \lambda_i)$ then $|A - xI| = \prod_i (\lambda_i - x)$. -/
Statement charpolyH_eq_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ)
    (h : A.charpoly = ∏ i, (X - C (l i))) : charpolyH A = ∏ i, (C (l i) - X) := by
  Hint "Each factor $\\lambda_i - x$ is $-(x - \\lambda_i)$: there are $n$ minus signs."
  Hint (hidden := true) "`have e : ∏ i, (C (l i) - X) = ∏ i, -(X - C (l i)) := by simp_rw [neg_sub]`."
  have e : ∏ i, (C (l i) - X) = ∏ i, -(X - C (l i)) := by
    simp only [neg_sub]
  Hint (hidden := true) "`rw [charpolyH_eq, h, e, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]`."
  rw [charpolyH_eq, h, e, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

end LinearAlgebraGame

Conclusion "$p(x) = (\\lambda_1 - x)(\\lambda_2 - x)\\cdots(\\lambda_n - x)$."

NewTheorem neg_sub Finset.prod_neg Finset.card_univ
TheoremTab "Eigen"
