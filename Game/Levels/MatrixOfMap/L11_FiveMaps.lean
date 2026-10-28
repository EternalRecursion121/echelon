import Game.Levels.MatrixOfMap.L10_LIso

World "MatrixOfMap"
Level 11
Title "Five maps of the plane"

-- @sheet 8 Q1b
/-! @answer
By part (a), $\mathcal L(\mathbb R^2, \mathbb R^2) \cong \mathcal M_{2\times 2}$, which has
dimension $4$. In a $4$-dimensional space any five vectors are linearly dependent, so there
are $c_1,\dots,c_5$, not all zero, with $c_1t_1 + \dots + c_5t_5 = 0$ — the zero map.
-/
Introduction "
**Problem Sheet 8, Question 1(b).** Show that it follows that for any five transformations
$t_1, \\dots, t_5 : \\mathbb R^2 \\to \\mathbb R^2$ there are scalars $c_1, \\dots, c_5 \\in \\mathbb R$
such that not every $c_i$ equals $0$ but $c_1 t_1 + \\dots + c_5 t_5$ is the zero map.

`LinearMap.toMatrix'` is the isomorphism of part (a) for the standard bases.
"

namespace LinearAlgebraGame

/-- Any five linear maps $\mathbb R^2 \to \mathbb R^2$ satisfy a nontrivial linear relation. -/
Statement (t : Fin 5 → ((Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) :
    ∃ c : Fin 5 → ℝ, c ≠ 0 ∧ ∑ i, c i • t i = 0 := by
  Hint "First compute the dimension of the space of maps, using the isomorphism with matrices."
  Hint (hidden := true) "`have hdim : Module.finrank ℝ ((Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = 4`,
  proved by `rw [(LinearMap.toMatrix' : ((Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) ≃ₗ[ℝ] _).finrank_eq,
  Module.finrank_matrix]` and `simp`."
  have hdim : Module.finrank ℝ ((Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = 4 := by
    rw [(LinearMap.toMatrix' : ((Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) ≃ₗ[ℝ] _).finrank_eq,
      Module.finrank_matrix]
    simp
  Hint "Five vectors in a four-dimensional space cannot be independent."
  Hint (hidden := true) "`have hdep : ¬ LinearIndependent ℝ t`: assume `hli`, then
  `hli.fintype_card_le_finrank` says $5 \\le 4$."
  have hdep : ¬ LinearIndependent ℝ t := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [hdim] at this
    simp at this
  Hint (hidden := true) "`rw [Fintype.not_linearIndependent_iff] at hdep` gives the relation:
  `obtain ⟨c, hc, i, hi⟩ := hdep`."
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hc, i, hi⟩ := hdep
  refine ⟨c, ?_, hc⟩
  intro h0
  apply hi
  rw [h0]
  exact rfl

end LinearAlgebraGame

Conclusion "
Dimension counting at work: $\\dim\\mathcal L(\\mathbb R^2,\\mathbb R^2) = 4 < 5$.
"

NewTheorem Module.finrank_matrix
NewDefinition LinearMap.toMatrix'
TheoremTab "Matrices"
