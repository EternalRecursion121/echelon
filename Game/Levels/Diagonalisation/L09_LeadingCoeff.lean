import Game.Levels.Diagonalisation.L08_OddSize

World "Diagonalisation"
Level 9
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
(`Matrix.charpoly_monic`, `Matrix.charpoly_natDegree_eq_dim`); `charpolyH_eq` relates
Hefferon's $|A - xI|$ to it.

So Lean checks your formula, but the permutation-expansion argument is yours: this is an
**explain level**. Inside your proof write that argument as a comment
block starting `-- Explain:` (the export puts it in your hand-in).

**Find** the coefficient: a formula $c(n)$, depending only on $n$, with
$\\operatorname{coeff}_{x^n}|A - xI| = c(n)$ for every $n \\times n$ matrix $A$.

*A Lean trap:* if `h : p.natDegree = n` and you try `rw [← h]`, Lean may complain that the
\"motive is not type correct\" — `n` also occurs in the *type* of `A`, which cannot be
rewritten. Rewrite the other way, in a hypothesis instead (`rw [h] at …`).
"

namespace LinearAlgebraGame

open Polynomial in
/-- There is a formula $c(n)$ for the coefficient of $x^n$ in $|A - xI|$, the same for every $n\times n$ matrix $A$. -/
Statement : ∃ c : ℕ → ℝ, ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), (charpolyH A).coeff n = c n := by
  -- Explain: in the permutation expansion of |A - xI| each term is a product of n entries, one
  -- from each row and column; only diagonal entries contain x, so only the identity permutation,
  -- (a₁₁ - x)⋯(aₙₙ - x), reaches degree n. Its x^n coefficient is (-1)^n.
  Hint "Which permutation in the expansion of $|A - xI|$ can reach degree $n$, and what is
  its coefficient of $x^n$? In Lean, compare with Mathlib's monic $\\det(xI - A)$."
  Hint (hidden := true) "$|A - xI| = (-1)^n \\det(xI - A)$, and $\\det(xI - A)$ is monic of degree $n$."
  Hint (hidden := true) "`use fun n => (-1) ^ n`, then `intro n A`."
  use fun n => (-1) ^ n
  intro n A
  Hint (hidden := true) "`rw [charpolyH_eq, show ((-1 : ℝ[X]) ^ n) = C ((-1) ^ n) by simp, coeff_C_mul]`."
  rw [charpolyH_eq, show ((-1 : ℝ[X]) ^ n) = C ((-1) ^ n) by simp, coeff_C_mul]
  Hint (hidden := true) "`have h := Polynomial.Monic.coeff_natDegree (Matrix.charpoly_monic A)`, then
  `rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h`."
  have h := Polynomial.Monic.coeff_natDegree (Matrix.charpoly_monic A)
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  Hint (hidden := true) "Model explanation: *each term of the permutation expansion is a product
  of $n$ entries, one from each row and column; only diagonal entries contain $x$, so only the
  identity permutation, $(a_\{11} - x)\\cdots(a_\{nn} - x)$, has degree $n$ (any other has at most
  $n - 2$ diagonal factors). Its coefficient of $x^n$ is $(-1)^n$.*"
  rw [h, mul_one]

end LinearAlgebraGame

Conclusion "The coefficient is $(-1)^n$: only the identity permutation reaches degree $n$."

NewTheorem LinearAlgebraGame.charpolyH_eq Polynomial.coeff_C_mul Matrix.charpoly_monic Polynomial.Monic.coeff_natDegree Matrix.charpoly_natDegree_eq_dim
NewDefinition Matrix.charpoly
TheoremTab "Eigen"
