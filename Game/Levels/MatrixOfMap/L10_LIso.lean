import Game.Levels.MatrixOfMap.L09_OneDim

World "MatrixOfMap"
Level 10
Title "Maps are matrices"

-- @sheet 8 Q1a
/-! @answer
Fix bases $B = \langle\vec\beta_1,\dots,\vec\beta_n\rangle$ of $V$ and $D$ of $W$. The map
$\mathcal L(V,W) \to \mathcal M_{m\times n}$, $h \mapsto \mathrm{Rep}_{B,D}(h)$, is an isomorphism:
it is linear because $\mathrm{Rep}_D$ is ($\mathrm{Rep}_{B,D}(ah + bk)$ has columns
$\mathrm{Rep}_D(a h(\vec\beta_j) + b k(\vec\beta_j))$); it is one-to-one because a map is determined
by the images of a basis; it is onto because any matrix $H$ is the representation of the map
sending $\vec\beta_j$ to $\sum_i h_{ij}\vec\delta_i$, extended linearly.
-/
Introduction "
**Problem Sheet 8, Question 1(a).** Let $V$ and $W$ be vector spaces of dimensions $n$ and $m$.
The space $\\mathcal L(V, W)$ of linear maps from $V$ to $W$ is isomorphic to $\\mathcal M_{m\\times n}$.
Exhibit an isomorphism.

\"Dimension $n$\" is given as a basis `B` indexed by `Fin n`. You must exhibit an
isomorphism `e : (V →ₗ[ℝ] W) ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ` — and, so that it is *the*
natural one, show that `e h` represents `h`.
"

namespace LinearAlgebraGame

/-- There is an isomorphism $\mathcal L(V,W) \cong \mathcal M_{m\times n}$ sending each $h$ to a
matrix representing it. -/
Statement {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {m n : ℕ} (B : Module.Basis (Fin n) ℝ V) (D : Module.Basis (Fin m) ℝ W) :
    ∃ e : (V →ₗ[ℝ] W) ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ, ∀ h, IsRep B D h (e h) := by
  Hint "Which map from maps to matrices have you met in this world? Mathlib already knows it
  is a linear isomorphism."
  Hint (hidden := true) "`use LinearMap.toMatrix B D`, then the bridge level `isRep_toMatrix`."
  use LinearMap.toMatrix B D
  intro h
  exact isRep_toMatrix B D h

end LinearAlgebraGame

Conclusion "
$h \\mapsto \\mathrm{Rep}_{B,D}(h)$ is the isomorphism; in particular
$\\dim \\mathcal L(V, W) = mn$.
"

TheoremTab "Matrices"
