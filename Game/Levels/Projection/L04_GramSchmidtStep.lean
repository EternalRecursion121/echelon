import Game.Levels.Projection.L03_OrthogonalIndependent

World "Projection"
Level 4
Title "One Gram–Schmidt step"

Introduction "
The Gram–Schmidt process (Hefferon Theorem Three.VI.2.7) replaces a basis by an orthogonal one,
one vector at a time: $\\vec\\kappa_1 = \\vec\\beta_1$ and
$$\\vec\\kappa_2 = \\vec\\beta_2 - \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec\\beta_2).$$
Show that this one step produces a vector orthogonal to $\\vec\\kappa_1$ **and** does not change
the span: $[\\vec\\beta_1, \\vec\\kappa_2] = [\\vec\\beta_1, \\vec\\beta_2]$.

For spans: `Submodule.span_le` reduces `span S ≤ W` to `S ⊆ W`; `Set.insert_subset_iff` and
`Set.singleton_subset_iff` split a set like `{a, b}`; and `Submodule.subset_span`,
`Submodule.add_mem`, `Submodule.sub_mem`, `Submodule.smul_mem` show membership.
"

namespace LinearAlgebraGame

open Matrix in
/-- $\vec\kappa_2 = \vec\beta_2 - \mathrm{proj}_{[\vec\beta_1]}(\vec\beta_2)$ is orthogonal to
$\vec\beta_1$, and $[\vec\beta_1, \vec\kappa_2] = [\vec\beta_1, \vec\beta_2]$. -/
Statement {n : ℕ} (β₁ β₂ : Fin n → ℝ) (h₁ : β₁ ≠ 0) :
    let κ₂ := β₂ - projLine β₁ β₂
    κ₂ ⬝ᵥ β₁ = 0 ∧ Submodule.span ℝ {β₁, κ₂} = Submodule.span ℝ {β₁, β₂} := by
  constructor
  · Hint (hidden := true) "This is your first level of this world."
    exact projLine_orth β₁ β₂ h₁
  · Hint "Two inclusions: `apply le_antisymm`. $\\vec\\kappa_2$ is a combination of the
    $\\vec\\beta$'s, and $\\vec\\beta_2 = \\vec\\kappa_2 + \\mathrm\{proj}$."
    apply le_antisymm
    · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      constructor
      · exact Submodule.subset_span (by simp)
      · apply Submodule.sub_mem
        · exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      constructor
      · exact Submodule.subset_span (by simp)
      · Hint (hidden := true) "`have : β₂ = κ₂ + projLine β₁ β₂ := by simp [κ₂]`, then
        `rw [this]` and `Submodule.add_mem`."
        have : β₂ = κ₂ + projLine β₁ β₂ := by simp [κ₂]
        rw [this]
        apply Submodule.add_mem
        · exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact Submodule.subset_span (by simp)

end LinearAlgebraGame

Conclusion "
Repeating the step — subtract from each new $\\vec\\beta_i$ its projections onto all the
$\\vec\\kappa$'s so far — is the Gram–Schmidt process.
"

NewTheorem Set.insert_subset_iff Set.singleton_subset_iff
TheoremTab "Projection"

