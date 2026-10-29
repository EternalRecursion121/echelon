import Game.Metadata
import Game.Ch3a

World "Homomorphisms"
Level 1
Title "A homomorphism sends zero to zero"

Introduction "
A **homomorphism** (linear map) $h : V \\to W$ (Hefferon Definition Three.II.1.1) preserves
addition and scalar multiplication — it need not be a correspondence. In Lean it is an element
`h : V →ₗ[ℝ] W`, and `map_add` / `map_smul` are its two defining properties.

Lemma Three.II.1.6: $h(\\vec 0) = \\vec 0$. Hefferon's proof: $h(\\vec 0) = h(0\\cdot\\vec 0) = 0\\cdot h(\\vec 0) = \\vec 0$.
"

namespace LinearAlgebraGame

/-- A linear map sends $\vec 0$ to $\vec 0$. -/
Statement hom_map_zero {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (h : V →ₗ[ℝ] W) : h 0 = 0 := by
  Hint "Write $\\vec 0$ as the scalar $0$ times a vector, then pull the scalar out."
  Hint (hidden := true) "`calc h 0 = h ((0 : ℝ) • (0 : V)) := by rw [zero_smul]`
  `_ = (0 : ℝ) • h 0 := by rw [map_smul]`
  `_ = 0 := by rw [zero_smul]`"
  calc h 0 = h ((0 : ℝ) • (0 : V)) := by rw [zero_smul]
    _ = (0 : ℝ) • h 0 := by rw [map_smul]
    _ = 0 := by rw [zero_smul]

end LinearAlgebraGame

Conclusion "
From now on `hom_map_zero` is in your inventory.
"

DisabledTheorem map_zero LinearMap.map_zero
DisabledTactic simp norm_num
TheoremTab "Maps"
NewTheorem sub_eq_add_neg neg_one_smul
