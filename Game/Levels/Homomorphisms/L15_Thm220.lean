import Game.Levels.Homomorphisms.L14_RightInverse

World "Homomorphisms"
Level 15
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

You already have (1) ⇔ (3) (`LinearMap.ker_eq_bot`) and (1) ⇔ (4) (`inj_iff_rank`). New tools:
`LinearEquiv.ofInjective h hi : V ≃ₗ[ℝ] range h`, `B.linearIndependent`,
`LinearIndependent.map'`, `Fintype.linearIndependent_iff`.
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
  · Hint (hidden := true) "`exact LinearMap.ker_eq_bot.symm`"
    exact LinearMap.ker_eq_bot.symm
  · Hint "(1) ⇔ (4): you proved it with $\\dim V$ in place of $n$; the basis has $n$ vectors."
    Hint (hidden := true) "`rw [inj_iff_rank, Module.finrank_eq_card_basis B, Fintype.card_fin]`"
    rw [inj_iff_rank, Module.finrank_eq_card_basis B, Fintype.card_fin]
  · constructor
    · intro hi
      Hint "A one-to-one map sends independent sets to independent sets."
      Hint (hidden := true) "`exact B.linearIndependent.map' h (LinearMap.ker_eq_bot.mpr {hi})`"
      exact B.linearIndependent.map' h (LinearMap.ker_eq_bot.mpr hi)
    · intro hli
      Hint "Show the null space is trivial: if $h(c_1\\vec\\beta_1+\\dots+c_n\\vec\\beta_n) = \\vec 0$ then
      $c_1 h(\\vec\\beta_1)+\\dots+c_n h(\\vec\\beta_n) = \\vec 0$, so all $c_i = 0$."
      Hint (hidden := true) "`rw [inj_iff_kernel]`, `intro v hv`, `rw [← B.sum_repr v, map_sum] at hv`,
      `simp only [map_smul] at hv`."
      rw [inj_iff_kernel]
      intro v hv
      rw [← B.sum_repr v, map_sum] at hv
      simp only [map_smul] at hv
      Hint (hidden := true) "`have hc := Fintype.linearIndependent_iff.mp {hli} _ {hv}`, then
      `rw [← B.sum_repr v]` and `simp only [hc, zero_smul, Finset.sum_const_zero]`."
      have hc := Fintype.linearIndependent_iff.mp hli _ hv
      rw [← B.sum_repr v]
      simp only [hc, zero_smul, Finset.sum_const_zero]

end LinearAlgebraGame

Conclusion "
Theorem 2.20 is yours. In particular a one-to-one map from an $n$-dimensional space is an
isomorphism onto its range, which is $n$-dimensional.
"

NewTheorem LinearAlgebraGame.inj_iff_kernel LinearEquiv.symm_apply_apply Module.Basis.linearIndependent LinearIndependent.map' Finset.sum_const_zero
NewDefinition LinearMap.rangeRestrict

DisabledTactic norm_num
TheoremTab "Dimension"
