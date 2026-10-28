import Game.Levels.Homomorphisms.L08_InjKernel

World "Homomorphisms"
Level 9
Title "Rank–nullity"

Introduction "
**Theorem Three.II.2.14 (rank–nullity).** For $h : V \\to W$ with $V$ finite-dimensional,
$$\\operatorname{rank}(h) + \\operatorname{nullity}(h) = \\dim V.$$
It is granted (inventory: `LinearMap.finrank_range_add_finrank_ker`). Use it: a linear map
$\\mathbb R^5 \\to \\mathbb R^3$ has nullity at least $2$.

Also useful: `Submodule.finrank_le` (a subspace is no bigger than the space) and
`Module.finrank_fin_fun` ($\\dim \\mathbb R^n = n$).
"

namespace LinearAlgebraGame

/-- Every linear map $\mathbb R^5 \to \mathbb R^3$ has nullity at least $2$. -/
Statement (h : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) :
    2 ≤ Module.finrank ℝ (LinearMap.ker h) := by
  Hint "rank + nullity = 5, and the rank is at most $\\dim \\mathbb R^3 = 3$."
  Hint (hidden := true) "`have hrn := LinearMap.finrank_range_add_finrank_ker h` and
  `have hle := Submodule.finrank_le (LinearMap.range h)`."
  have hrn := LinearMap.finrank_range_add_finrank_ker h
  have hle := Submodule.finrank_le (LinearMap.range h)
  Hint (strict := true) (hidden := true) "`rw [Module.finrank_fin_fun] at hrn hle`, then `omega`."
  rw [Module.finrank_fin_fun] at hrn hle
  omega

end LinearAlgebraGame

Conclusion "
So such a map can never be one-to-one: it kills at least a plane.
"

NewTheorem LinearMap.finrank_range_add_finrank_ker

TheoremTab "Dimension"
