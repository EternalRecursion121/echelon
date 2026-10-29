import Game.Levels.Subspaces.L01_SubspaceTest

World "Subspaces"
Level 2
Title "Two planes"

Introduction "
In $\\mathbb{R}^3$, the plane $x + y + z = 0$ through the origin is a subspace, but the
parallel plane $x + y + z = 1$ is not. Vectors of $\\mathbb{R}^3$ are `v : Fin 3 → ℝ` with
components `v 0`, `v 1`, `v 2`.

Membership `v ∈ {v | P v}` unfolds to `P v` with `rw [Set.mem_ofPred_eq]`.

**Subspace vs. its set.** In `(W : Set (Fin 3 → ℝ)) = {v | …}` the left side is the *set of
vectors* of the subspace `W`; Lean displays it as `↑W`. The subspace `W` and the set `↑W` look
alike but are different objects, so from `hW : ↑W = S` a plain `rw [hW]` will not touch
`0 ∈ W`. The granted lemma `mem_iff_of_coe_eq hW : x ∈ W ↔ x ∈ S` bridges them:
`rw [mem_iff_of_coe_eq hW] at h`.
"

namespace LinearAlgebraGame

/-- The plane $x+y+z=0$ is a subspace of $\mathbb{R}^3$; the plane $x+y+z=1$ is not. -/
Statement : (∃ W : Submodule ℝ (Fin 3 → ℝ),
      (W : Set (Fin 3 → ℝ)) = {v | v 0 + v 1 + v 2 = 0}) ∧
    ¬ ∃ W : Submodule ℝ (Fin 3 → ℝ), (W : Set (Fin 3 → ℝ)) = {v | v 0 + v 1 + v 2 = 1} := by
  constructor
  · Hint "Use the subspace test."
    apply subspace_test
    · Hint "Nonempty: name an element."
      use 0
      norm_num
    · intro c₁ c₂ s₁ s₂ h1 h2
      Hint (hidden := true) "`rw [Set.mem_ofPred_eq] at {h1} {h2} ⊢`, then
      `simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`, then `linear_combination`."
      rw [Set.mem_ofPred_eq] at h1 h2 ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination c₁ * h1 + c₂ * h2
  · Hint "Every subspace contains $\\vec 0$. Does this plane?"
    intro h
    obtain ⟨W, hW⟩ := h
    Hint (hidden := true) "`have h0 := W.zero_mem`, then `rw [mem_iff_of_coe_eq {hW}] at h0`
    and `norm_num at h0`."
    have h0 := W.zero_mem
    rw [mem_iff_of_coe_eq hW] at h0
    norm_num at h0

end LinearAlgebraGame

Conclusion "
The quickest way to show a set is *not* a subspace is usually: it misses $\\vec 0$.
"

TheoremTab "Subspaces"
NewTheorem LinearAlgebraGame.subspace_test Set.mem_ofPred_eq Submodule.zero_mem LinearAlgebraGame.mem_iff_of_coe_eq
