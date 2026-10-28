import Game.Levels.FromScratch.L02_OwnSubspaceTest

World "FromScratch"
Level 3
Title "Your own span"

Introduction "
The game's `spanOf v` is the set of all linear combinations $\\sum_i c_i\\vec v_i$ of finitely
many vectors (Definition Two.I.2.13). Lemma Two.I.2.15 says it is a subspace. Prove that
with your own `IsSubsp`.

To add two combinations, add their coefficient vectors: $\\sum a_i\\vec v_i + \\sum b_i\\vec v_i
= \\sum (a_i + b_i)\\vec v_i$.
"

namespace LinearAlgebraGame

/-- The span of $\vec v_0, \ldots, \vec v_{n-1}$ is a subspace. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (v : Fin n → V) :
    IsSubsp (spanOf v) := by
  constructor
  · Hint "$\\vec 0$ is the combination with all coefficients $0$."
    use 0
    simp
  · intro x y hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    Hint (hidden := true) "`use a + b`, then `simp [add_smul, Finset.sum_add_distrib]`."
    use a + b
    simp [add_smul, Finset.sum_add_distrib]
  · intro c x hx
    obtain ⟨a, rfl⟩ := hx
    Hint (hidden := true) "`use c • a`, then `simp [Finset.smul_sum, smul_smul]`."
    use c • a
    simp [Finset.smul_sum, smul_smul]

end LinearAlgebraGame

Conclusion "Combinations of combinations are combinations."

NewDefinition LinearAlgebraGame.spanOf
NewTheorem LinearAlgebraGame.mem_spanOf
TheoremTab "From Scratch"
