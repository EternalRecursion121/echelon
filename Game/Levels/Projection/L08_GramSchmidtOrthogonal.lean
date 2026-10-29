import Game.Levels.Projection.L07_FloatingAngle

World "Projection"
Level 8
Title "Gram–Schmidt: orthogonality"

Introduction "
Hefferon Theorem Three.VI.2.7 for three vectors: with
$$\\vec\\kappa_1 = \\vec\\beta_1,\\quad \\vec\\kappa_2 = \\vec\\beta_2 - \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec\\beta_2),\\quad
\\vec\\kappa_3 = \\vec\\beta_3 - \\mathrm{proj}_{[\\vec\\kappa_1]}(\\vec\\beta_3) - \\mathrm{proj}_{[\\vec\\kappa_2]}(\\vec\\beta_3),$$
the $\\vec\\kappa$'s are mutually orthogonal (this level) and span the same space as the
$\\vec\\beta$'s (the boss).

The projections need nonzero vectors to project onto: we assume $\\vec\\beta_1 \\ne \\vec 0$ and
$\\vec\\kappa_2 \\ne \\vec 0$ (both automatic when the $\\vec\\beta$'s are independent).
"

namespace LinearAlgebraGame

open Matrix in
/-- The Gram–Schmidt vectors $\vec\kappa_1, \vec\kappa_2, \vec\kappa_3$ are mutually orthogonal. -/
Statement {n : ℕ} (β₁ β₂ β₃ : Fin n → ℝ) (h1 : β₁ ≠ 0) :
    let κ₁ := β₁
    let κ₂ := β₂ - projLine κ₁ β₂
    let κ₃ := β₃ - projLine κ₁ β₃ - projLine κ₂ β₃
    κ₂ ≠ 0 → κ₂ ⬝ᵥ κ₁ = 0 ∧ κ₃ ⬝ᵥ κ₁ = 0 ∧ κ₃ ⬝ᵥ κ₂ = 0 := by
  intro h2
  Hint "The first one is your first level of this world."
  have o21 : κ₂ ⬝ᵥ κ₁ = 0 := projLine_orth κ₁ β₂ h1
  refine ⟨o21, ?_, ?_⟩
  · Hint "$\\vec\\kappa_3\\cdot\\vec\\kappa_1 = (\\vec\\beta_3 - \\mathrm\{proj}_\{[\\vec\\kappa_1]})\\cdot\\vec\\kappa_1
    - \\mathrm\{proj}_\{[\\vec\\kappa_2]}(\\vec\\beta_3)\\cdot\\vec\\kappa_1$. The first is zero by
    `projLine_orth`, the second because $\\vec\\kappa_2 \\perp \\vec\\kappa_1$."
    Hint (hidden := true) "`simp only [κ₃]`, then `rw [sub_dotProduct, projLine_orth κ₁ β₃ {h1},
    projLine, smul_dotProduct, o21, smul_zero, sub_zero]`."
    simp only [κ₃]
    rw [sub_dotProduct, projLine_orth κ₁ β₃ h1, projLine, smul_dotProduct, o21, smul_zero,
      sub_zero]
  · Hint "Same idea, with the two projections the other way round."
    Hint (hidden := true) "Swap the two subtractions with `sub_right_comm` first. Careful:
    a bare `dotProduct_comm` rewrites the first dot product it finds; say which one,
    `dotProduct_comm κ₁ κ₂`."
    simp only [κ₃]
    rw [sub_right_comm, sub_dotProduct, projLine_orth κ₂ β₃ h2, projLine, smul_dotProduct,
      dotProduct_comm κ₁ κ₂, o21, smul_zero, sub_zero]

end LinearAlgebraGame

Conclusion "
Each new $\\vec\\kappa$ is orthogonal to the earlier ones because we subtracted exactly its
components along them.
"

NewTheorem sub_right_comm
DisabledTheorem InnerProductSpace.gramSchmidt_orthogonal
TheoremTab "Projection"
