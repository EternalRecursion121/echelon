import Game.Levels.BasisDim.L02_BasisIff

World "BasisDim"
Level 3
Title "A basis for 𝒫₂"

-- @sheet 3 Q7
/-! @answer
The standard basis $\langle 1, x, x^2\rangle$ is a basis of $\mathcal P_2$: every
$a_0 + a_1x + a_2x^2$ is the combination with coefficients $a_0, a_1, a_2$, and these are the
only coefficients that work (compare coefficients of $1$, $x$, $x^2$). By Theorem 1.12 it is a
basis.
-/
Introduction "
**Problem Sheet 3, Question 7** (first half). Find a basis for $\\mathcal P_2$, the space of
all quadratic polynomials.

In this game $\\mathcal P_2$ is `Poly 2`: a polynomial $a_0 + a_1x + a_2x^2$ is stored as its
coefficient vector `![a₀, a₁, a₂]`. You supply a basis — its size $k$ and the sequence
`b : Fin k → Poly 2` — with `use k, b`, then prove it is a basis of the whole space `⊤`.
Theorem 1.12 (`isBasisOf_top_iff`) lets you prove that by unique representation.
"

namespace LinearAlgebraGame

/-- $\mathcal P_2$ has a basis $b_1, \dots, b_k$. -/
Statement : ∃ k : ℕ, ∃ b : Fin k → Poly 2, IsBasisOf b ⊤ := by
  Hint "Which polynomials can you combine to get every $a_0 + a_1x + a_2x^2$, in only one way?
  Supply them with `use`."
  Hint (hidden := true) "`use 3, ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]` is $\\langle 1, x, x^2\\rangle$."
  use 3, ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
  Hint "Use Theorem 1.12 (unique representation): for each $x$, give the coefficients and show
  they are the only ones."
  Hint (hidden := true) "`rw [isBasisOf_top_iff]`, `intro x`."
  rw [isBasisOf_top_iff]
  intro x
  Hint (hidden := true) "The coefficients of $x$ in the standard basis are $x$ itself:
  `refine ⟨x, ?_, ?_⟩`."
  refine ⟨x, ?_, ?_⟩
  · Hint (hidden := true) "`entrywise <;> simp [Fin.sum_univ_three]`."
    entrywise <;> simp [Fin.sum_univ_three]
  · intro c hc
    Hint (hidden := true) "Read off each coordinate of `{hc}`: `funext i`, `fin_cases i`,
    then `simp [← {hc}, Fin.sum_univ_three]`."
    funext i
    fin_cases i <;> simp [← hc, Fin.sum_univ_three]

end LinearAlgebraGame

Conclusion "
$\\langle 1, x, x^2\\rangle$ is a basis of $\\mathcal P_2$: it has one polynomial of each
degree. Must every basis?
"

NewTheorem LinearAlgebraGame.isBasisOf_top_iff
TheoremTab "Basis"
NewDefinition LinearAlgebraGame.Poly
