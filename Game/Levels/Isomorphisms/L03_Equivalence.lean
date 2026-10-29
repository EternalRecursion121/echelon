import Game.Levels.Isomorphisms.L02_InverseLinear

World "Isomorphisms"
Level 3
Title "An equivalence relation"

Introduction "
Write $V \\cong W$ for \"there is an isomorphism $V \\to W$\"; in Lean that is
`Nonempty (V ≃ₗ[ℝ] W)`. Lean already provides the three constructions:

* `LinearEquiv.refl ℝ V : V ≃ₗ[ℝ] V` (the identity),
* `e.symm` (the inverse — linear by the previous level),
* `e.trans f` (the composite: first `e`, then `f`).

Assemble them into Hefferon Lemma Three.I.2.1: $\\cong$ is reflexive, symmetric and transitive.

`Nonempty X` means \"there is some element of `X`\". To prove it, give one in angle brackets:
`exact ⟨e⟩`. To use a hypothesis `Nonempty X`, take its element out: `rintro ⟨e⟩` (or
`obtain ⟨e⟩ := h`).
"

namespace LinearAlgebraGame

/-- Isomorphism is reflexive, symmetric and transitive. -/
Statement {U V W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] :
    Nonempty (V ≃ₗ[ℝ] V) ∧ (Nonempty (V ≃ₗ[ℝ] W) → Nonempty (W ≃ₗ[ℝ] V)) ∧
    (Nonempty (U ≃ₗ[ℝ] V) → Nonempty (V ≃ₗ[ℝ] W) → Nonempty (U ≃ₗ[ℝ] W)) := by
  Hint "Three separate claims: reflexive, symmetric, transitive."
  Hint (hidden := true) "Split with `refine ⟨?_, ?_, ?_⟩`."
  refine ⟨?_, ?_, ?_⟩
  · Hint (hidden := true) "`exact ⟨LinearEquiv.refl ℝ V⟩`"
    exact ⟨LinearEquiv.refl ℝ V⟩
  · Hint (hidden := true) "`rintro ⟨e⟩` names the isomorphism; then `exact ⟨e.symm⟩`."
    rintro ⟨e⟩
    exact ⟨e.symm⟩
  · Hint (hidden := true) "`rintro ⟨e⟩ ⟨f⟩`, then `exact ⟨e.trans f⟩`."
    rintro ⟨e⟩ ⟨f⟩
    exact ⟨e.trans f⟩

end LinearAlgebraGame

Conclusion "
So it makes sense to say two spaces are *isomorphic* without saying which comes first.
"

NewDefinition LinearEquiv LinearEquiv.refl LinearEquiv.symm LinearEquiv.trans
DisabledTactic simp norm_num
TheoremTab "Isomorphisms"
NewTheorem LinearEquiv.injective
