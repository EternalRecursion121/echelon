import Game.Levels.Dimension.L01_RootsA

World "Dimension"
Level 2
Title "Quadratics vanishing at 5 and 3"

-- @sheet 4 Q6b
/-! @answer
$p(5) = p(3) = 0$ iff $(x-5)(x-3) = x^2 - 8x + 15$ divides $p$; since $\deg p \le 2$ this
means $p = c(x^2 - 8x + 15)$. So the subspace is $[\{x^2 - 8x + 15\}]$; a single nonzero
polynomial is independent. **Basis $\langle x^2 - 8x + 15\rangle$, dimension 1.**
(Concretely, $a_0 + 5a_1 + 25a_2 = 0$ and $a_0 + 3a_1 + 9a_2 = 0$ give $a_1 = -8a_2$,
$a_0 = 15a_2$.)
-/
Introduction "
**Problem Sheet 4, Question 6(b).** The subspace of $p(x)$ such that $p(5) = 0$, and
$p(3) = 0$. *Hint: How do factorisations of such $p(x)$ look like?*

The subspace is the intersection `⊓` of two kernels. Membership of `U ⊓ W` is a pair of
memberships. As before, you supply a basis and prove it.
"

namespace LinearAlgebraGame

/-- $\{p \in\mathcal P_2 \mid p(5) = p(3) = 0\}$ has a basis $b_1, \dots, b_k$, and
dimension $k$. -/
Statement : ∃ k : ℕ, ∃ b : Fin k → Poly 2,
    IsBasisOf b (LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3)) ∧
    Module.finrank ℝ ↥(LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3)) = k := by
  Hint "Follow the sheet's hint: what do the factorisations of such $p$ look like? Find a basis
  on paper and prove the basis claim with `have`."
  Hint (hidden := true) "`have hB : IsBasisOf ![![15, -8, 1]] (LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓
  LinearMap.ker (Poly.evalAt 3)) := by` — that is $\\langle (x-5)(x-3)\\rangle$."
  have hB : IsBasisOf ![![15, -8, 1]]
      (LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3)) := by
    constructor
    · Hint "One nonzero vector is independent: look at a nonzero coefficient."
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h2 := congrFun hg 2
      simp at h2
      fin_cases i
      exact h2
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        constructor <;> simp [Poly.evalAt_apply, Poly.eval, Fin.sum_univ_three] <;> norm_num
      · Hint "Two linear equations on $(a_0, a_1, a_2)$: solve them, and write $p$ as a combination
        of your basis."
        intro p hp
        obtain ⟨h5, h3⟩ := hp
        simp [Poly.evalAt_apply, Poly.eval, Fin.sum_univ_three] at h5 h3
        rw [Submodule.mem_span_range_iff_exists_fun]
        Hint (hidden := true) "`refine ⟨![p 2], ?_⟩`, then compare coefficients with `linarith`."
        refine ⟨![p 2], ?_⟩
        entrywise <;> simp <;> linarith
  Hint (hidden := true) "`exact ⟨1, _, hB, hB.finrank_eq⟩`"
  exact ⟨1, _, hB, hB.finrank_eq⟩

end LinearAlgebraGame

Conclusion "
Basis $\\langle x^2 - 8x + 15 \\rangle = \\langle (x-5)(x-3)\\rangle$, dimension 1.
"

TheoremTab "Dimension"
