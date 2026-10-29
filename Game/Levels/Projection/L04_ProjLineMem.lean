import Game.Levels.Projection.L03_OrthogonalIndependent

World "Projection"
Level 4
Title "Projections stay in the subspace"

Introduction "
$\\mathrm{proj}_{[\\vec s\\,]}(\\vec v)$ is a multiple of $\\vec s$. So if $\\vec s$ lies in a
subspace $W$, so does every projection onto it — whatever $\\vec v$ is.

This small fact does all the span bookkeeping in Gram–Schmidt (the next levels): each
$\\vec\\kappa_i$ is a $\\vec\\beta_i$ minus projections onto earlier $\\vec\\kappa$'s, so it stays
in any subspace containing the $\\vec\\beta$'s.
"

namespace LinearAlgebraGame

open Matrix in
/-- If $\vec s \in W$ then $\mathrm{proj}_{[\vec s]}(\vec v) \in W$. -/
Statement projLine_mem {n : ℕ} {W : Submodule ℝ (Fin n → ℝ)} {s : Fin n → ℝ} (v : Fin n → ℝ)
    (hs : s ∈ W) : projLine s v ∈ W := by
  Hint "Unfold `projLine`: it is a scalar times $\\vec s$."
  Hint (hidden := true) "`rw [projLine]`, then `apply Submodule.smul_mem` and `exact {hs}`."
  rw [projLine]
  apply Submodule.smul_mem
  exact hs

end LinearAlgebraGame

Conclusion "
`projLine_mem v hs : projLine s v ∈ W` is now in your inventory (the subspace $W$ is read off
from `hs : s ∈ W`).
"

TheoremTab "Projection"
