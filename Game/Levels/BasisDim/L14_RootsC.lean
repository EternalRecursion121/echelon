import Game.Levels.BasisDim.L13_RootsB

World "BasisDim"
Level 14
Title "Quadratics vanishing at 5, 3 and 1"

-- @sheet 4 Q6c
/-! @answer
If $p(5) = p(3) = p(1) = 0$ then $p$ has the three roots $5, 3, 1$, but a nonzero polynomial
of degree $\le 2$ has at most two roots; so $p = 0$. (Directly: by (b), $p = c(x-5)(x-3)$, and
$p(1) = 8c = 0$ forces $c = 0$.) The subspace is $\{0\}$: **basis the empty sequence
$\langle\,\rangle$, dimension 0.**
-/
Introduction "
**Problem Sheet 4, Question 6(c).** The subspace of $p(x)$ such that $p(5) = 0$, $p(3) = 0$,
and $p(1) = 0$.

The empty sequence is `![]` (indexed by `Fin 0`). Its span is the trivial subspace `⊥`:
`Set.range_eq_empty` and `Submodule.span_empty` help, and `linearIndependent_empty_type`
says the empty sequence is independent.
"

namespace LinearAlgebraGame

/-- The empty sequence is a basis of $\{p \in\mathcal P_2 \mid p(5) = p(3) = p(1) = 0\}$, which
has dimension 0. -/
Statement : IsBasisOf (![] : Fin 0 → Poly 2)
      (LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3) ⊓
        LinearMap.ker (Poly.evalAt 1)) ∧
    Module.finrank ℝ ↥(LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3) ⊓
        LinearMap.ker (Poly.evalAt 1)) = 0 := by
  Hint "Show the subspace is trivial: a quadratic with three roots is zero."
  have hB : IsBasisOf (![] : Fin 0 → Poly 2)
      (LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3) ⊓
        LinearMap.ker (Poly.evalAt 1)) := by
    constructor
    · exact linearIndependent_empty_type
    · symm
      rw [Set.range_eq_empty, Submodule.span_empty, eq_bot_iff]
      intro p hp
      obtain ⟨⟨h5, h3⟩, h1⟩ := hp
      simp [Poly.evalAt_apply, Poly.eval, Fin.sum_univ_three] at h5 h3 h1
      rw [Submodule.mem_bot]
      Hint (hidden := true) "Three equations, three unknowns: `ext i; fin_cases i <;> simp <;> linarith`."
      ext i
      fin_cases i <;> simp <;> linarith
  exact ⟨hB, hB.finrank_eq⟩

end LinearAlgebraGame

Conclusion "
Only the zero polynomial: basis $\\langle\\,\\rangle$, dimension 0.
"

TheoremTab "Dimension"
NewTheorem linearIndependent_empty_type Set.range_eq_empty Submodule.span_empty eq_bot_iff Submodule.mem_bot symm
