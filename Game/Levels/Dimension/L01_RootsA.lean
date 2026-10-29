import Game.Metadata
import Game.Ch2b
import Game.Levels.BasisDim

World "Dimension"
Level 1
Title "Quadratics vanishing at 5"

-- @sheet 4 Q6a
/-! @answer
$p(5) = 0$ iff $(x - 5)$ divides $p$, i.e. $p = (x-5)(bx + c) = c(x - 5) + b(x^2 - 5x)$.
So $\{p \in \mathcal P_2 \mid p(5) = 0\}$ is spanned by $x - 5$ and $x^2 - 5x$; these are
independent (comparing the $x^2$ and constant coefficients of $a(x-5) + b(x^2 - 5x) = 0$
gives $b = 0$, $a = 0$). **Basis $\langle x - 5, x^2 - 5x\rangle$, dimension 2.**
(Concretely, $a_0 + a_1x + a_2x^2$ with $a_0 + 5a_1 + 25a_2 = 0$ equals
$(a_1 + 5a_2)(x - 5) + a_2(x^2 - 5x)$.)
-/
Introduction "
**Problem Sheet 4, Question 6.** Find a basis for, and the dimension of, each of these
subspaces of the space $\\mathcal P_2$ of quadratic polynomials.
**(a)** The subspace of quadratic polynomials $p(x)$ such that $p(5) = 0$.

In `Poly 2`, $a_0 + a_1x + a_2x^2$ is `![a₀, a₁, a₂]`. `Poly.evalAt 5` is the linear map
$p \\mapsto p(5)$, so the subspace is its kernel. `Poly.evalAt_apply` and `Poly.eval` unfold
an evaluation into $\\sum_i a_i 5^i$.

In `Poly.evalAt (n := 2) 5` the syntax `(n := 2)` passes the argument named `n` explicitly
(we evaluate polynomials of $\\mathcal P_2$). Lean may display `LinearMap.ker f` as `f.ker`. You supply a basis — its size $k$ and the
sequence `b : Fin k → Poly 2` — and prove it is a basis; `IsBasisOf.finrank_eq` then turns the
basis into the dimension.
"

namespace LinearAlgebraGame

/-- $\{p \in \mathcal P_2 \mid p(5) = 0\}$ has a basis $b_1, \dots, b_k$, and dimension $k$. -/
Statement : ∃ k : ℕ, ∃ b : Fin k → Poly 2,
    IsBasisOf b (LinearMap.ker (Poly.evalAt (n := 2) 5)) ∧
    Module.finrank ℝ (LinearMap.ker (Poly.evalAt (n := 2) 5)) = k := by
  Hint "Which polynomials vanish at 5? Factor them. Find a basis on paper, then prove the basis
  claim as a separate fact with `have`; the dimension then follows."
  Hint (hidden := true) "`have hB : IsBasisOf ![![-5, 1, 0], ![0, -5, 1]]
  (LinearMap.ker (Poly.evalAt (n := 2) 5)) := by` — that is $\\langle x - 5, x^2 - 5x\\rangle$."
  have hB : IsBasisOf ![![-5, 1, 0], ![0, -5, 1]] (LinearMap.ker (Poly.evalAt (n := 2) 5)) := by
    constructor
    · Hint "Independence: compare constant and $x^2$ coefficients."
      rw [LinearIndependent.pair_iff]
      intro s t h
      have h0 := congrFun h 0
      have h2 := congrFun h 2
      simp at h0 h2
      constructor <;> linarith
    · apply le_antisymm
      · Hint "Both basis polynomials vanish at 5."
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        Hint (hidden := true) "`fin_cases i <;> simp [Poly.evalAt_apply, Poly.eval, Fin.sum_univ_three] <;> norm_num`"
        fin_cases i <;> simp [Poly.evalAt_apply, Poly.eval, Fin.sum_univ_three] <;> norm_num
      · Hint "Given $p$ with $p(5) = 0$, write it as a combination of your basis."
        Hint (hidden := true) "The coefficients are $a_1 + 5a_2$ and $a_2$."
        intro p hp
        simp [Poly.evalAt_apply, Poly.eval, Fin.sum_univ_three] at hp
        rw [Submodule.mem_span_range_iff_exists_fun]
        Hint (hidden := true) "`refine ⟨![p 1 + 5 * p 2, p 2], ?_⟩`, then compare coefficients."
        refine ⟨![p 1 + 5 * p 2, p 2], ?_⟩
        ext i
        fin_cases i <;> simp <;> linarith
  Hint (hidden := true) "`exact ⟨2, _, hB, hB.finrank_eq⟩`"
  exact ⟨2, _, hB, hB.finrank_eq⟩

end LinearAlgebraGame

Conclusion "
Basis $\\langle x - 5, x^2 - 5x\\rangle$, dimension 2.
"

NewDefinition LinearAlgebraGame.Poly.evalAt LinearAlgebraGame.Poly.eval
TheoremTab "Dimension"
NewTheorem LinearAlgebraGame.Poly.evalAt_apply LinearAlgebraGame.IsBasisOf.finrank_eq LinearMap.mem_ker
