import Game.Levels.Homomorphisms.L07_KernelRange

World "Homomorphisms"
Level 8
Title "One-to-one iff the null space is trivial"

Introduction "
Theorem Three.II.2.20, (1) ⇔ (3): a homomorphism is one-to-one if and only if its null space
is trivial, i.e. only $\\vec 0$ maps to $\\vec 0$.
"

namespace LinearAlgebraGame

/-- $h$ is one-to-one iff $h(\vec v) = \vec 0$ implies $\vec v = \vec 0$. -/
Statement inj_iff_kernel {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (h : V →ₗ[ℝ] W) :
    Function.Injective h ↔ ∀ v, h v = 0 → v = 0 := by
  constructor
  · intro hi v hv
    Hint "Both $\\vec v$ and $\\vec 0$ map to $\\vec 0$."
    Hint (hidden := true) "`apply {hi}`, then `rw [{hv}, hom_map_zero]`."
    apply hi
    rw [hv, hom_map_zero]
  · intro hk u v huv
    Hint "If $h(\\vec u) = h(\\vec v)$, what is $h(\\vec u - \\vec v)$?"
    Hint (hidden := true) "`have : {u} - {v} = 0 := by apply {hk}; rw [map_sub, {huv}, sub_self]`"
    have : u - v = 0 := by
      apply hk
      rw [map_sub, huv, sub_self]
    Hint (strict := true) (hidden := true) "`exact sub_eq_zero.mp this`"
    exact sub_eq_zero.mp this

end LinearAlgebraGame

Conclusion "
In Mathlib's language: `LinearMap.ker_eq_bot : ker h = ⊥ ↔ Function.Injective h`, now in your
inventory ($\\bot$ is the trivial subspace).
"

DisabledTheorem injective_iff_map_eq_zero injective_iff_map_eq_zero' LinearMap.ker_eq_bot'
DisabledTactic simp norm_num
TheoremTab "Maps"
NewTheorem LinearMap.ker_eq_bot sub_eq_zero
