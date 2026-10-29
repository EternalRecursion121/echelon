import Game.Levels.Dimension.L02_RootsB

World "Dimension"
Level 3
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
says the empty sequence is independent. `bot_le : ⊥ ≤ W` holds for every subspace.
"

namespace LinearAlgebraGame

/-- A basis $b_1, \dots, b_k$ of $\{p \in\mathcal P_2 \mid p(5) = p(3) = p(1) = 0\}$, which
has dimension $k$. -/
Statement : ∃ k : ℕ, ∃ b : Fin k → Poly 2,
    IsBasisOf b (LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3) ⊓
        LinearMap.ker (Poly.evalAt 1)) ∧
    Module.finrank ℝ ↥(LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3) ⊓
        LinearMap.ker (Poly.evalAt 1)) = k := by
  Hint "What can you say about a quadratic with these roots? Find a basis on paper, then
  supply its size and the basis with `use`."
  Hint (hidden := true) "`use 0, ![]`"
  use 0, ![]
  Hint "Now prove your basis claim with `have`; the dimension then follows."
  have hB : IsBasisOf (![] : Fin 0 → Poly 2)
      (LinearMap.ker (Poly.evalAt (n := 2) 5) ⊓ LinearMap.ker (Poly.evalAt 3) ⊓
        LinearMap.ker (Poly.evalAt 1)) := by
    constructor
    · exact linearIndependent_empty_type
    · Hint "The span of the empty sequence is `⊥`. Show the subspace is `⊥` too."
      Hint (hidden := true) "`rw [Set.range_eq_empty, Submodule.span_empty]`, then
      `apply le_antisymm bot_le` leaves `K ≤ ⊥`."
      rw [Set.range_eq_empty, Submodule.span_empty]
      apply le_antisymm bot_le
      intro p hp
      obtain ⟨⟨h5, h3⟩, h1⟩ := hp
      Hint "`{h5}` reads `p ∈ ↑(ker …)`: the `↑` views the subspace as a set, so `LinearMap.mem_ker`
        does not match yet. `rw [SetLike.mem_coe, LinearMap.mem_ker, Poly.evalAt_apply] at {h5}`
        removes it, or `simp [Poly.evalAt_apply, Poly.eval, Fin.sum_univ_three] at {h5}` writes it
        out as an equation in the coefficients (same for the others)."
      simp [Poly.evalAt_apply, Poly.eval, Fin.sum_univ_three] at h5 h3 h1
      Hint (hidden := true) "`rw [Submodule.mem_bot]`: show $p = 0$."
      rw [Submodule.mem_bot]
      Hint (hidden := true) "Three equations, three unknowns: `entrywise <;> linarith`."
      entrywise <;> linarith
  exact ⟨hB, hB.finrank_eq⟩

end LinearAlgebraGame

Conclusion "
Only the zero polynomial: basis $\\langle\\,\\rangle$, dimension 0.
"

TheoremTab "Dimension"
NewTheorem linearIndependent_empty_type Set.range_eq_empty Submodule.span_empty bot_le Submodule.mem_bot
