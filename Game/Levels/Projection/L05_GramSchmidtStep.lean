import Game.Levels.Projection.L04_ProjLineMem

World "Projection"
Level 5
Title "One Gram–Schmidt step"

Introduction "
**Why orthogonal bases?** If $\\langle\\vec\\kappa_1, \\dots, \\vec\\kappa_k\\rangle$ is an orthogonal
basis, coordinates need no linear system: dotting $\\vec v = c_1\\vec\\kappa_1 + \\dots + c_k\\vec\\kappa_k$
with $\\vec\\kappa_i$ kills every term but one, so
$$c_i = \\frac{\\vec v\\cdot\\vec\\kappa_i}{\\vec\\kappa_i\\cdot\\vec\\kappa_i},\\qquad
\\vec v = \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec v) + \\dots + \\mathrm{proj}_{[\\vec\\kappa_k]}(\\vec v).$$
The Gram–Schmidt process (Hefferon Theorem Three.VI.2.7) produces such a basis from any basis,
one vector at a time: $\\vec\\kappa_1 = \\vec\\beta_1$ and
$$\\vec\\kappa_2 = \\vec\\beta_2 - \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec\\beta_2).$$
Show that this one step produces a vector orthogonal to $\\vec\\kappa_1$ **and** does not change
the span: $[\\vec\\beta_1, \\vec\\kappa_2] = [\\vec\\beta_1, \\vec\\beta_2]$.
"

namespace LinearAlgebraGame

open Matrix in
/-- $\vec\kappa_2 = \vec\beta_2 - \mathrm{proj}_{[\vec\beta_1]}(\vec\beta_2)$ is orthogonal to
$\vec\beta_1$, and $[\vec\beta_1, \vec\kappa_2] = [\vec\beta_1, \vec\beta_2]$. -/
Statement {n : ℕ} (β₁ β₂ : Fin n → ℝ) (h1 : β₁ ≠ 0) :
    let κ₂ := β₂ - projLine β₁ β₂
    κ₂ ⬝ᵥ β₁ = 0 ∧ Submodule.span ℝ {β₁, κ₂} = Submodule.span ℝ {β₁, β₂} := by
  constructor
  · Hint (hidden := true) "This is the first level of this world."
    exact projLine_orth β₁ β₂ h1
  · Hint "Two inclusions (`apply le_antisymm`). A span is inside a subspace when its generators
    are. $\\vec\\kappa_2$ is $\\vec\\beta_2$ minus a projection onto $\\vec\\beta_1$, and
    $\\vec\\beta_2 = \\vec\\kappa_2 + \\mathrm\{proj}$: use `projLine_mem` for the projections."
    Hint (hidden := true) "For each inclusion: `rw [Submodule.span_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]` leaves one membership per generator. Generators of the span are
    members by `Submodule.subset_span (by simp)`; combine with `Submodule.sub_mem`,
    `Submodule.add_mem` and `projLine_mem`."
    apply le_antisymm
    · have m1 : β₁ ∈ Submodule.span ℝ {β₁, β₂} := Submodule.subset_span (by simp)
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      constructor
      · exact m1
      · apply Submodule.sub_mem
        · exact Submodule.subset_span (by simp)
        · exact projLine_mem β₂ m1
    · have n1 : β₁ ∈ Submodule.span ℝ {β₁, κ₂} := Submodule.subset_span (by simp)
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      constructor
      · exact n1
      · Hint (hidden := true) "`have e2 : β₂ = κ₂ + projLine β₁ β₂ := by simp [κ₂]`, then
        `rw [e2]` and `Submodule.add_mem`."
        have e2 : β₂ = κ₂ + projLine β₁ β₂ := by simp [κ₂]
        rw [e2]
        apply Submodule.add_mem
        · exact Submodule.subset_span (by simp)
        · exact projLine_mem β₂ n1

end LinearAlgebraGame

Conclusion "
Repeating the step — subtract from each new $\\vec\\beta_i$ its projections onto all the
$\\vec\\kappa$'s so far — is the Gram–Schmidt process.
"

NewTheorem Set.insert_subset_iff Set.singleton_subset_iff
TheoremTab "Projection"
