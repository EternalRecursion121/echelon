import Game.Levels.Homomorphisms.L10_InjRank
import Game.Levels.BasisDim

World "Homomorphisms"
Level 11
Title "Onto iff rank is dim W"

-- @sheet 6 Q4a
/-! @answer
By Lemma 2.1 the range $\mathscr R(h)$ is a subspace of $W$. If $h$ is onto then
$\mathscr R(h) = W$, so $\operatorname{rank}(h) = \dim\mathscr R(h) = \dim W$. Conversely if
$\dim\mathscr R(h) = \dim W$ then $\mathscr R(h)$ is a subspace of $W$ of full dimension, hence
equals $W$ (Sheet 4 Q10b: a basis of $\mathscr R(h)$ is then a linearly independent set of
$\dim W$ vectors in $W$, so a basis of $W$); that is, $h$ is onto.
-/
Introduction "
**Problem Sheet 6, Question 4(a).** Let $h : V \\to W$ be a homomorphism. Use Lemma 2.1 of
Section Three.II to prove that $h$ is onto if and only if its rank equals the dimension of $W$.

Lemma 2.1 gives that the range is a subspace `LinearMap.range h` of $W$;
`LinearMap.range_eq_top` says onto ⇔ range $= W$ (written `⊤`). Sheet 4 Q10(b) is your
`eq_iff_finrank_eq_of_le` (Basis & Dimension world): for `h : U ≤ W`,
`finrank U = finrank W ↔ U = W`. Apply it with $W = $ `⊤`; `le_top : U ≤ ⊤` holds for every
subspace. ($W$ is assumed finite-dimensional, as the sheet's
use of $\\dim W$ requires.)
"

namespace LinearAlgebraGame

/-- $h$ is onto iff $\operatorname{rank} h = \dim W$. -/
Statement onto_iff_rank {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [FiniteDimensional ℝ W] (h : V →ₗ[ℝ] W) :
    Function.Surjective h ↔ Module.finrank ℝ (LinearMap.range h) = Module.finrank ℝ W := by
  Hint "Onto means the range is all of $W$."
  Hint (hidden := true) "`rw [← LinearMap.range_eq_top]`, then `constructor`."
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h1
    Hint (hidden := true) "`rw [{h1}, finrank_top]`"
    rw [h1, finrank_top]
  · intro h2
    Hint "A subspace of full dimension is the whole space."
    Hint (hidden := true) "`rw [← eq_iff_finrank_eq_of_le (LinearMap.range h) ⊤ le_top,
    finrank_top]`, then `exact {h2}`."
    rw [← eq_iff_finrank_eq_of_le (LinearMap.range h) ⊤ le_top, finrank_top]
    exact h2

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 6 Q4(a):** onto ⇔ $\\mathscr R(h) = W$ ⇔ $\\dim\\mathscr R(h) = \\dim W$, the last
step because $\\mathscr R(h)$ is a subspace of $W$.
"

NewTheorem finrank_top le_top
DisabledTheorem Submodule.eq_top_of_finrank_eq Submodule.eq_of_le_of_finrank_eq Submodule.eq_of_le_of_finrank_le
DisabledTactic simp norm_num
TheoremTab "Dimension"
