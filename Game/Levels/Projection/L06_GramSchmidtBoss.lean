import Game.Levels.Projection.L05_FloatingGramSchmidt

World "Projection"
Level 6
Title "Gram–Schmidt"

Introduction "
**Boss.** Hefferon Theorem Three.VI.2.7 for three vectors: with
$$\\vec\\kappa_1 = \\vec\\beta_1,\\quad \\vec\\kappa_2 = \\vec\\beta_2 - \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec\\beta_2),\\quad
\\vec\\kappa_3 = \\vec\\beta_3 - \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec\\beta_3) - \\mathrm{proj}_{[\\vec\\kappa_2]}(\\vec\\beta_3),$$
the $\\vec\\kappa$'s are mutually orthogonal and span the same space as the $\\vec\\beta$'s.

The projections need nonzero vectors to project onto: we assume $\\vec\\beta_1 \\ne \\vec 0$ and
$\\vec\\kappa_2 \\ne \\vec 0$ (both automatic when the $\\vec\\beta$'s are independent).
Together with *Orthogonal vectors are independent*, this makes the $\\vec\\kappa$'s an
orthogonal basis of $[\\vec\\beta_1, \\vec\\beta_2, \\vec\\beta_3]$ whenever they are nonzero.
"

namespace LinearAlgebraGame

open Matrix in
/-- Gram–Schmidt on three vectors gives mutually orthogonal vectors with the same span. -/
Statement {n : ℕ} (β₁ β₂ β₃ : Fin n → ℝ) (h1 : β₁ ≠ 0) :
    let κ₁ := β₁
    let κ₂ := β₂ - projLine κ₁ β₂
    let κ₃ := β₃ - projLine κ₁ β₃ - projLine κ₂ β₃
    κ₂ ≠ 0 →
    (κ₂ ⬝ᵥ κ₁ = 0 ∧ κ₃ ⬝ᵥ κ₁ = 0 ∧ κ₃ ⬝ᵥ κ₂ = 0) ∧
    Submodule.span ℝ {κ₁, κ₂, κ₃} = Submodule.span ℝ {β₁, β₂, β₃} := by
  intro h2
  have o21 : κ₂ ⬝ᵥ κ₁ = 0 := projLine_orth κ₁ β₂ h1
  refine ⟨⟨o21, ?_, ?_⟩, ?_⟩
  · Hint "$\\vec\\kappa_3\\cdot\\vec\\kappa_1 = (\\vec\\beta_3 - \\mathrm\{proj}_\{[\\vec\\kappa_1]})\\cdot\\vec\\kappa_1
    - \\mathrm\{proj}_\{[\\vec\\kappa_2]}(\\vec\\beta_3)\\cdot\\vec\\kappa_1$. The first is zero by
    `projLine_orth`, the second because $\\vec\\kappa_2 \\perp \\vec\\kappa_1$."
    Hint (hidden := true) "`simp only [κ₃]`, then `rw [sub_dotProduct, projLine_orth κ₁ β₃ {h1},
    projLine, smul_dotProduct, o21, smul_zero, sub_zero]`."
    simp only [κ₃]
    rw [sub_dotProduct, projLine_orth κ₁ β₃ h1, projLine, smul_dotProduct, o21, smul_zero,
      sub_zero]
  · Hint (hidden := true) "Swap the two subtractions with `sub_right_comm` first."
    simp only [κ₃]
    rw [sub_right_comm, sub_dotProduct, projLine_orth κ₂ β₃ h2, projLine, smul_dotProduct,
      dotProduct_comm κ₁ κ₂, o21, smul_zero, sub_zero]
  · Hint "As in *One Gram–Schmidt step*, two inclusions. It helps to know $\\vec\\kappa_2$ lies
    in the $\\vec\\beta$-span before dealing with $\\vec\\kappa_3$."
    apply le_antisymm
    · have m2 : κ₂ ∈ Submodule.span ℝ {β₁, β₂, β₃} := by
        apply Submodule.sub_mem
        · exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact Submodule.subset_span (by simp [κ₁])
      rw [Submodule.span_le, Set.insert_subset_iff, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      refine ⟨Submodule.subset_span (by simp [κ₁]), m2, ?_⟩
      apply Submodule.sub_mem
      · apply Submodule.sub_mem
        · exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact Submodule.subset_span (by simp [κ₁])
      · apply Submodule.smul_mem
        exact m2
    · Hint (hidden := true) "Write $\\vec\\beta_2$ and $\\vec\\beta_3$ back in terms of the
      $\\vec\\kappa$'s: `have e3 : β₃ = κ₃ + projLine κ₁ β₃ + projLine κ₂ β₃ := by
      simp only [κ₃]; module`."
      have e2 : β₂ = κ₂ + projLine κ₁ β₂ := by
        simp only [κ₂]
        module
      have e3 : β₃ = κ₃ + projLine κ₁ β₃ + projLine κ₂ β₃ := by
        simp only [κ₃]
        module
      rw [Submodule.span_le, Set.insert_subset_iff, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      refine ⟨Submodule.subset_span (by simp [κ₁]), ?_, ?_⟩
      · rw [e2]
        apply Submodule.add_mem
        · exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact Submodule.subset_span (by simp)
      · rw [e3]
        apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact Submodule.subset_span (by simp)
          · apply Submodule.smul_mem
            exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact Submodule.subset_span (by simp)

end LinearAlgebraGame

Conclusion "
That is Gram–Schmidt: an orthogonal basis of the same span, built one projection at a time.
"

NewTheorem sub_right_comm
DisabledTheorem InnerProductSpace.gramSchmidt_orthogonal InnerProductSpace.span_gramSchmidt
TheoremTab "Projection"
