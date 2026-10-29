import Game.Levels.BasisDim.L09_RankZero

World "BasisDim"
Level 10
Title "Subspaces are no bigger"

-- @sheet 4 Q10a
/-! @answer
Take a basis $\langle\vec\beta_1,\dots,\vec\beta_k\rangle$ of $U$, $k = \dim U$. Since
$U \subseteq W$, these are vectors of $W$, and they are still linearly independent there
(independence does not depend on the surrounding space). An independent set in $W$ has at
most $\dim W$ elements (it extends to a basis of $W$), so $\dim U = k \le \dim W$.
-/
Introduction "
**Problem Sheet 4, Question 10.** Consider how *dimension* interacts with *subset*. Assume
$U$ and $W$ are both subspaces of some vector space, and that $U \\subseteq W$.
**(a)** Prove that $\\dim(U) \\le \\dim(W)$.

`Module.finrank ℝ U` is $\\dim U$. Caution: `finrank` is defined to be $0$ for an
infinite-dimensional space, so we assume the ambient space $V$ is finite-dimensional (part (c)
is about the infinite-dimensional case).

Useful: an injective linear map sends an independent set to an independent set, so it cannot
increase dimension (`LinearMap.finrank_le_finrank_of_injective`). Which injective linear map
goes from $U$ to $W$?
"

namespace LinearAlgebraGame

/-- If $U \subseteq W$ then $\dim U \le \dim W$. -/
Statement finrank_le_of_le {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (U W : Submodule ℝ V) (h : U ≤ W) : Module.finrank ℝ U ≤ Module.finrank ℝ W := by
  Hint "Every independent sequence in $U$ is an independent sequence in $W$. In map
  language: the inclusion $U \\to W$ is injective."
  Hint (hidden := true) "The inclusion $U \\hookrightarrow W$ is `Submodule.inclusion h`, and
  `Submodule.inclusion_injective h` says it is injective."
  Hint (hidden := true) "`exact LinearMap.finrank_le_finrank_of_injective
  (Submodule.inclusion_injective h)`"
  exact LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective h)

end LinearAlgebraGame

Conclusion "
$\\dim U \\le \\dim W$: `finrank_le_of_le` is in your inventory. (Mathlib calls it
`Submodule.finrank_mono`; you will meet that name in later worlds.)
"

NewTheorem LinearMap.finrank_le_finrank_of_injective Submodule.inclusion_injective

DisabledTheorem Submodule.finrank_mono Submodule.finrank_le_finrank_of_le
DisabledTactic simp norm_num
TheoremTab "Dimension"
NewDefinition Module.finrank
