import Game.Levels.Isomorphisms.L01_Dilation

World "Isomorphisms"
Level 2
Title "The inverse of an isomorphism"

Introduction "
Isomorphism is an **equivalence relation** (Hefferon Lemma Three.I.2.1). Reflexivity and
transitivity are easy: the identity is an isomorphism, and a composite of isomorphisms is one.
The one step with content is **symmetry**: if $f : V \\to W$ is an isomorphism then its
inverse function $f^{-1} : W \\to V$ is again *linear*.

Here $f$ is linear and $g$ is a two-sided inverse function of $f$ — nothing is assumed about
$g$'s linearity. Prove that $g$ preserves $+$ and $\\cdot$.
"

namespace LinearAlgebraGame

/-- If $f : V \to W$ is linear with two-sided inverse function $g$, then $g$ is linear. -/
Statement {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (g : W → V) (hgf : ∀ v, g (f v) = v) (hfg : ∀ w, f (g w) = w) :
    (∀ w₁ w₂, g (w₁ + w₂) = g w₁ + g w₂) ∧ ∀ (r : ℝ) w, g (r • w) = r • g w := by
  constructor
  · intro w₁ w₂
    Hint "Idea: write $\\vec w_1 = f(g(\\vec w_1))$ and $\\vec w_2 = f(g(\\vec w_2))$; then
    $\\vec w_1 + \\vec w_2 = f(g(\\vec w_1) + g(\\vec w_2))$ because $f$ is linear, and $g$ undoes $f$."
    Hint (hidden := true) "`calc g ({w₁} + {w₂}) = g (f (g {w₁}) + f (g {w₂})) := by rw [hfg, hfg]`
    `_ = g (f (g {w₁} + g {w₂})) := by rw [map_add]`
    `_ = g {w₁} + g {w₂} := by rw [hgf]`"
    calc g (w₁ + w₂) = g (f (g w₁) + f (g w₂)) := by rw [hfg, hfg]
      _ = g (f (g w₁ + g w₂)) := by rw [map_add]
      _ = g w₁ + g w₂ := by rw [hgf]
  · intro r w
    Hint "Same trick: $r\\vec w = r f(g(\\vec w)) = f(r\\, g(\\vec w))$."
    Hint (hidden := true) "`calc g ({r} • {w}) = g ({r} • f (g {w})) := by rw [hfg]`, then `map_smul`, then `hgf`."
    calc g (r • w) = g (r • f (g w)) := by rw [hfg]
      _ = g (f (r • g w)) := by rw [map_smul]
      _ = r • g w := by rw [hgf]

end LinearAlgebraGame

Conclusion "
So the inverse of an isomorphism is an isomorphism. Lean packages this: for
`e : V ≃ₗ[ℝ] W`, `e.symm : W ≃ₗ[ℝ] V` is the inverse isomorphism.
"

DisabledTactic simp norm_num
TheoremTab "Maps"
NewTheorem map_add map_smul
