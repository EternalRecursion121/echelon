import Game.Levels.Homomorphisms.L02_Subtraction

World "Homomorphisms"
Level 3
Title "A non-example"

Introduction "
Hefferon's non-example: the map $\\mathbb R^2 \\to \\mathbb R$ given by
$(x, y) \\mapsto 2x - 3y + 1$ is **not** linear. Prove that no linear map has these values.
"

namespace LinearAlgebraGame

/-- There is no linear map $h : \mathbb R^2 \to \mathbb R$ with $h(x,y) = 2x - 3y + 1$. -/
Statement : ¬ ∃ h : (Fin 2 → ℝ) →ₗ[ℝ] ℝ, ∀ v, h v = 2 * v 0 - 3 * v 1 + 1 := by
  Hint "Where does such a map send $\\vec 0$? Where must a linear map send it?"
  Hint (hidden := true) "`rintro ⟨h, hh⟩`, then `have h0 := hh 0`."
  rintro ⟨h, hh⟩
  have h0 := hh 0
  Hint (strict := true) (hidden := true) "`rw [hom_map_zero] at {h0}`, then `norm_num at {h0}`."
  rw [hom_map_zero] at h0
  norm_num at h0

end LinearAlgebraGame

Conclusion "
The map sends $\\vec 0$ to $1 \\neq 0$. The \"$+1$\" makes it *affine*, not linear.
"

NewTheorem LinearAlgebraGame.hom_map_zero map_sub
DisabledTheorem map_zero LinearMap.map_zero
TheoremTab "Maps"
