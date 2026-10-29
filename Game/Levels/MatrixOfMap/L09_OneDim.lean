import Game.Levels.MatrixOfMap.L08_Composition

World "MatrixOfMap"
Level 9
Title "Composition in one dimension"

-- @sheet 7 Q3
/-! @answer
**Yes, in every one-dimensional space.** On $\mathbb R^1$ every linear map is $x \mapsto ax$, and
$a(bx) = b(ax)$. In general, let $V$ have dimension 1 with basis $\langle\vec v\rangle$. Every
vector is $c\vec v$, and every linear $t$ satisfies $t(\vec v) = a\vec v$ for some scalar $a$, so
$t(c\vec v) = ca\vec v$: every map is multiplication by a scalar. If $f(\vec v) = a\vec v$ and
$g(\vec v) = b\vec v$ then $f(g(c\vec v)) = cba\,\vec v = cab\,\vec v = g(f(c\vec v))$, because
multiplication of reals commutes.
-/
Introduction "
**Problem Sheet 7, Question 3.** Show that composition of linear transformations on
$\\mathbb R^1$ is commutative. Is this true for all one-dimensional spaces?

Here $V$ is any space of dimension 1 ($\\mathbb R^1$ is one of them). Decide first:
`left` if composition on $V$ can fail to commute, `right` if it always commutes. Then prove it.

`hV` is about the whole space $V$, not a subspace, so use `finrank_eq_one_iff'` (new):
`finrank_eq_one_iff'.mp hV : ∃ v, v ≠ 0 ∧ ∀ w, ∃ c, c • v = w` — like
`exists_line_of_finrank_eq_one`, but with no `⊤` or `∈` to get through.
"

namespace LinearAlgebraGame

/-- On a one-dimensional space, does $f \circ g = g \circ f$ for all linear $f, g$? -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (hV : Module.finrank ℝ V = 1) :
    (¬ ∀ f g : V →ₗ[ℝ] V, f ∘ₗ g = g ∘ₗ f) ∨ (∀ f g : V →ₗ[ℝ] V, f ∘ₗ g = g ∘ₗ f) := by
  Hint "In dimension 1, what does a linear map do to a spanning vector $\\vec v$?"
  right
  intro f g
  Hint (hidden := true) "`finrank_eq_one_iff'` gives a nonzero `v` such that every vector is
  `c • v`: `obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp {hV}`."
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hV
  Hint "Write $f(\\vec v)$ and $g(\\vec v)$ as multiples of $\\vec v$."
  obtain ⟨a, ha⟩ := hv (f v)
  obtain ⟨b, hb⟩ := hv (g v)
  Hint (hidden := true) "Compare the maps on every vector: `apply LinearMap.ext`, `intro w`,
  and write `w = c • v` with `obtain ⟨c, rfl⟩ := hv w`."
  apply LinearMap.ext
  intro w
  obtain ⟨c, rfl⟩ := hv w
  Hint (hidden := true) "Unfold with `LinearMap.comp_apply` and `map_smul`, replace $f(\\vec v)$
  and $g(\\vec v)$ using `← {ha}` and `← {hb}`, and finish with `module`."
  rw [LinearMap.comp_apply, LinearMap.comp_apply, map_smul, map_smul, map_smul, map_smul,
    ← ha, ← hb, map_smul, map_smul, ← ha, ← hb]
  module

end LinearAlgebraGame

Conclusion "
**Yes**, in every one-dimensional space: all maps are multiplication by a scalar, and scalars
commute. (In dimension 2 it already fails.)
"

NewTheorem LinearMap.ext finrank_eq_one_iff'
TheoremTab "Matrices"
