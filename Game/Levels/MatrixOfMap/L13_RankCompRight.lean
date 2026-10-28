import Game.Levels.MatrixOfMap.L12_RankProductEx

World "MatrixOfMap"
Level 13
Title "Rank of g ∘ h, first bound"

-- @sheet 8 Q2b
/-! @answer
The range of $g\circ h$ is $g(\mathcal R(h))$, the image under $g$ of the range of $h$. The image
of an $n$-dimensional space under a linear map has dimension at most $n$ (it is spanned by the
images of a basis of $\mathcal R(h)$). So $\mathrm{rank}(g\circ h) = \dim g(\mathcal R(h)) \le n$.
-/
Introduction "
**Problem Sheet 8, Question 2(b).** Let $h : V \\to W$ and $g : W \\to X$. Show that if
$\\mathrm{rank}(h) = n$ then $\\mathrm{rank}(g \\circ h) \\le n$.

The rank of a map is the dimension of its range: `Module.finrank ℝ (LinearMap.range h)`.
"

namespace LinearAlgebraGame

/-- If $\operatorname{rank} h = n$ then $\operatorname{rank}(g\circ h) \le n$. -/
Statement {V W X : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (h : V →ₗ[ℝ] W) (g : W →ₗ[ℝ] X) (n : ℕ)
    (hn : Module.finrank ℝ (LinearMap.range h) = n) :
    Module.finrank ℝ (LinearMap.range (g ∘ₗ h)) ≤ n := by
  Hint "The range of $g\\circ h$ is the image under $g$ of the range of $h$."
  Hint (hidden := true) "`rw [LinearMap.range_comp, ← {hn}]`, then
  `exact Submodule.finrank_map_le g (LinearMap.range h)`."
  rw [LinearMap.range_comp, ← hn]
  exact Submodule.finrank_map_le g (LinearMap.range h)

end LinearAlgebraGame

Conclusion "
Applying a map can never raise dimension.
"

NewTheorem LinearMap.range_comp Submodule.finrank_map_le
TheoremTab "Matrices"
