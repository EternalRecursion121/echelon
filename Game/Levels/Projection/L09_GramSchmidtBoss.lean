import Game.Levels.Projection.L08_GramSchmidtOrthogonal

World "Projection"
Level 9
Title "Gram–Schmidt"

Introduction "
**Boss.** The other half of Hefferon Theorem Three.VI.2.7 for three vectors: the Gram–Schmidt
vectors
$$\\vec\\kappa_1 = \\vec\\beta_1,\\quad \\vec\\kappa_2 = \\vec\\beta_2 - \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec\\beta_2),\\quad
\\vec\\kappa_3 = \\vec\\beta_3 - \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec\\beta_3) - \\mathrm{proj}_{[\\vec\\kappa_2]}(\\vec\\beta_3)$$
span the same space as the $\\vec\\beta$'s. Together with the last level and *Orthogonal vectors
are independent*, this makes the $\\vec\\kappa$'s an orthogonal basis of
$[\\vec\\beta_1, \\vec\\beta_2, \\vec\\beta_3]$ whenever they are nonzero.

(No nonzero assumptions are needed here: Lean's `projLine` onto $\\vec 0$ is $\\vec 0$.)
"

namespace LinearAlgebraGame

open Matrix in
/-- Gram–Schmidt on three vectors does not change the span. -/
Statement {n : ℕ} (β₁ β₂ β₃ : Fin n → ℝ) :
    let κ₁ := β₁
    let κ₂ := β₂ - projLine κ₁ β₂
    let κ₃ := β₃ - projLine κ₁ β₃ - projLine κ₂ β₃
    Submodule.span ℝ {κ₁, κ₂, κ₃} = Submodule.span ℝ {β₁, β₂, β₃} := by
  Hint "As in *One Gram–Schmidt step*, two inclusions. Do the $\\vec\\kappa$'s in order: once
  you know $\\vec\\kappa_1, \\vec\\kappa_2$ are in a subspace, `projLine_mem` puts their
  projections there too."
  apply le_antisymm
  · Hint (hidden := true) "Record `have m1 : κ₁ ∈ Submodule.span ℝ \{β₁, β₂, β₃} :=
    Submodule.subset_span (by simp [κ₁])` and then `m2` for `κ₂` (with `Submodule.sub_mem` and
    `projLine_mem`), then `rw [Submodule.span_le, Set.insert_subset_iff, Set.insert_subset_iff,
    Set.singleton_subset_iff]`."
    have m1 : κ₁ ∈ Submodule.span ℝ {β₁, β₂, β₃} := Submodule.subset_span (by simp [κ₁])
    have m2 : κ₂ ∈ Submodule.span ℝ {β₁, β₂, β₃} :=
      Submodule.sub_mem _ (Submodule.subset_span (by simp)) (projLine_mem β₂ m1)
    have m3 : κ₃ ∈ Submodule.span ℝ {β₁, β₂, β₃} :=
      Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (projLine_mem β₃ m1)) (projLine_mem β₃ m2)
    rw [Submodule.span_le, Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨m1, m2, m3⟩
  · Hint (hidden := true) "Write $\\vec\\beta_2$ and $\\vec\\beta_3$ back in terms of the
    $\\vec\\kappa$'s: `have e3 : β₃ = κ₃ + projLine κ₁ β₃ + projLine κ₂ β₃ := by
    simp only [κ₃]; module`."
    have n1 : κ₁ ∈ Submodule.span ℝ {κ₁, κ₂, κ₃} := Submodule.subset_span (by simp)
    have n2 : κ₂ ∈ Submodule.span ℝ {κ₁, κ₂, κ₃} := Submodule.subset_span (by simp)
    have n3 : κ₃ ∈ Submodule.span ℝ {κ₁, κ₂, κ₃} := Submodule.subset_span (by simp)
    have e2 : β₂ = κ₂ + projLine κ₁ β₂ := by
      simp only [κ₂]
      module
    have e3 : β₃ = κ₃ + projLine κ₁ β₃ + projLine κ₂ β₃ := by
      simp only [κ₃]
      module
    rw [Submodule.span_le, Set.insert_subset_iff, Set.insert_subset_iff,
      Set.singleton_subset_iff, e2, e3]
    exact ⟨n1, Submodule.add_mem _ n2 (projLine_mem β₂ n1),
      Submodule.add_mem _ (Submodule.add_mem _ n3 (projLine_mem β₃ n1)) (projLine_mem β₃ n2)⟩

end LinearAlgebraGame

Conclusion "
That is Gram–Schmidt: an orthogonal basis of the same span, built one projection at a time.
"

DisabledTheorem InnerProductSpace.gramSchmidt_orthogonal InnerProductSpace.span_gramSchmidt
TheoremTab "Projection"
