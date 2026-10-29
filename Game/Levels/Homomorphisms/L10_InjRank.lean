import Game.Levels.Homomorphisms.L09_RankNullity

World "Homomorphisms"
Level 10
Title "One-to-one iff rank is dim V"

Introduction "
Theorem Three.II.2.20, (1) ⇔ (4): for $h : V \\to W$ with $V$ finite-dimensional, $h$ is one-to-one
if and only if $\\operatorname{rank}(h) = \\dim V$.

Useful: `LinearMap.ker_eq_bot : ker h = ⊥ ↔ Function.Injective h` (Mathlib's form of your
`inj_iff_kernel`, new in your inventory), `Submodule.finrank_eq_zero : finrank U = 0 ↔ U = ⊥`,
and rank–nullity.
"

namespace LinearAlgebraGame

/-- $h$ is one-to-one iff $\operatorname{rank} h = \dim V$. -/
Statement inj_iff_rank {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [FiniteDimensional ℝ V] (h : V →ₗ[ℝ] W) :
    Function.Injective h ↔ Module.finrank ℝ (LinearMap.range h) = Module.finrank ℝ V := by
  Hint "One-to-one ⇔ nullity $0$ ⇔ (by rank–nullity) rank $= \\dim V$."
  Hint (hidden := true) "`rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]`"
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  Hint (hidden := true) "`have := LinearMap.finrank_range_add_finrank_ker h`, then `omega`."
  have := LinearMap.finrank_range_add_finrank_ker h
  omega

end LinearAlgebraGame

Conclusion "
`inj_iff_rank` is now in your inventory.
"

NewTheorem LinearMap.ker_eq_bot
DisabledTheorem LinearMap.finrank_range_of_inj
DisabledTactic simp norm_num
TheoremTab "Dimension"
