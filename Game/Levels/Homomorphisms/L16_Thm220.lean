import Game.Levels.Homomorphisms.L15_IndepInj

World "Homomorphisms"
Level 16
Title "Theorem 2.20"

Introduction "
**Boss: Hefferon Theorem Three.II.2.20.** Let $h : V \\to W$ be linear with $\\dim V = n$ and let
$B = \\langle\\vec\\beta_1,\\dots,\\vec\\beta_n\\rangle$ be a basis of $V$. These are equivalent:

1. $h$ is one-to-one;
2. $h$ has a linear inverse from its range to its domain;
3. $\\mathscr N(h) = \\{\\vec 0\\}$;
4. $\\operatorname{rank}(h) = n$;
5. $\\langle h(\\vec\\beta_1),\\dots,h(\\vec\\beta_n)\\rangle$ is a basis of $\\mathscr R(h)$.

We prove each of (2)–(5) equivalent to (1). For (2), `h.rangeRestrict` is $h$ viewed as a map
into its range. For (5), the images always span $\\mathscr R(h)$, so being a basis means being
linearly independent — that is how (5) is stated.

You already have (1) ⇔ (3) (`LinearMap.ker_eq_bot`), (1) ⇔ (4) (`inj_iff_rank`) and
(5) ⇒ (1) (`inj_of_indep_images`). New tools: `LinearEquiv.ofInjective h hi : V ≃ₗ[ℝ] range h`
(an isomorphism onto the range); for an isomorphism `e`, `e.toLinearMap` is the same map viewed
as an ordinary linear map `→ₗ`, and `e.symm_apply_apply v : e.symm (e v) = v`;
`B.linearIndependent` (a basis is independent) and `LinearIndependent.map'` (a one-to-one map
keeps a sequence independent).
"

namespace LinearAlgebraGame

/-- Theorem 2.20: one-to-one ⇔ linear inverse on the range ⇔ trivial null space ⇔ rank $n$ ⇔ images of a basis are independent. -/
Statement {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ V] {n : ℕ} (B : Module.Basis (Fin n) ℝ V) (h : V →ₗ[ℝ] W) :
    (Function.Injective h ↔ ∃ g : LinearMap.range h →ₗ[ℝ] V, ∀ v, g (h.rangeRestrict v) = v) ∧
    (Function.Injective h ↔ LinearMap.ker h = ⊥) ∧
    (Function.Injective h ↔ Module.finrank ℝ (LinearMap.range h) = n) ∧
    (Function.Injective h ↔ LinearIndependent ℝ (fun i => h (B i))) := by
  Hint "Prove each condition equivalent to (1)."
  Hint (hidden := true) "Four equivalences: `refine ⟨?_, ?_, ?_, ?_⟩`."
  refine ⟨?_, ?_, ?_, ?_⟩
  · Hint "(1) ⇔ (2). Forward: $h$ is an isomorphism onto its range; invert it.
    Backward: a left inverse forces one-to-one."
    constructor
    · intro hi
      Hint (hidden := true) "`use (LinearEquiv.ofInjective h {hi}).symm.toLinearMap`, `intro v`,
      `exact (LinearEquiv.ofInjective h {hi}).symm_apply_apply v`."
      use (LinearEquiv.ofInjective h hi).symm.toLinearMap
      intro v
      exact (LinearEquiv.ofInjective h hi).symm_apply_apply v
    · Hint (hidden := true) "`rintro ⟨g, hg⟩ u v huv`, then `rw [← hg u, ← hg v]`."
      rintro ⟨g, hg⟩ u v huv
      rw [← hg u, ← hg v]
      Hint (hidden := true) "`congr 1`, `ext`, `exact {huv}`."
      congr 1
      ext
      exact huv
  · Hint (hidden := true) "`rw [LinearMap.ker_eq_bot]`"
    rw [LinearMap.ker_eq_bot]
  · Hint "(1) ⇔ (4): you proved it with $\\dim V$ in place of $n$; the basis has $n$ vectors."
    Hint (hidden := true) "`rw [inj_iff_rank, Module.finrank_eq_card_basis B, Fintype.card_fin]`"
    rw [inj_iff_rank, Module.finrank_eq_card_basis B, Fintype.card_fin]
  · constructor
    · intro hi
      Hint "A one-to-one map sends independent sets to independent sets."
      Hint (hidden := true) "`exact B.linearIndependent.map' h (LinearMap.ker_eq_bot.mpr {hi})`"
      exact B.linearIndependent.map' h (LinearMap.ker_eq_bot.mpr hi)
    · Hint "This is the previous level."
      Hint (hidden := true) "`exact inj_of_indep_images B h`"
      exact inj_of_indep_images B h

end LinearAlgebraGame

Conclusion "
Theorem 2.20 is yours. In particular a one-to-one map from an $n$-dimensional space is an
isomorphism onto its range, which is $n$-dimensional.
"

NewTheorem LinearAlgebraGame.inj_of_indep_images LinearEquiv.symm_apply_apply Module.Basis.linearIndependent LinearIndependent.map'
NewDefinition LinearMap.rangeRestrict LinearEquiv.ofInjective

DisabledTactic norm_num
TheoremTab "Dimension"
