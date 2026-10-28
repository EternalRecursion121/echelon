import Game.Levels.MatrixOfMap.L13_RankCompRight

World "MatrixOfMap"
Level 14
Title "Rank of g ∘ h, second bound"

-- @sheet 8 Q2c
/-! @answer
Every output $g(h(\vec v))$ of $g\circ h$ is an output of $g$, so
$\mathcal R(g\circ h) \subseteq \mathcal R(g)$. A subspace has dimension at most that of the
space containing it, so $\mathrm{rank}(g\circ h) \le \mathrm{rank}(g) = n$. Together with (b),
the rank of a product of matrices is at most the minimum of their ranks.
-/
Introduction "
**Problem Sheet 8, Question 2(c).** Let $h : V \\to W$ and $g : W \\to X$. Show that if
$\\mathrm{rank}(g) = n$ then $\\mathrm{rank}(g \\circ h) \\le n$.
"

namespace LinearAlgebraGame

/-- If $\operatorname{rank} g = n$ then $\operatorname{rank}(g\circ h) \le n$. -/
Statement {V W X : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ W]
    (h : V →ₗ[ℝ] W) (g : W →ₗ[ℝ] X) (n : ℕ)
    (hn : Module.finrank ℝ (LinearMap.range g) = n) :
    Module.finrank ℝ (LinearMap.range (g ∘ₗ h)) ≤ n := by
  Hint "Every output of $g \\circ h$ is an output of $g$."
  Hint (hidden := true) "`rw [← {hn}]`, then `Submodule.finrank_mono` applied to
  `LinearMap.range_comp_le_range h g`."
  rw [← hn]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range h g)

end LinearAlgebraGame

Conclusion "
So $\\mathrm{rank}(GH) \\le \\min(\\mathrm{rank}\\,G, \\mathrm{rank}\\,H)$.
"

NewTheorem LinearMap.range_comp_le_range
TheoremTab "Matrices"
