import Game.Levels.Homomorphisms.L14_RightInverse

World "Homomorphisms"
Level 15
Title "Independent images make a map one-to-one"

Introduction "
A warm-up for the boss, Theorem 2.20 (5) ⇒ (1): if $B = \\langle\\vec\\beta_1,\\dots,\\vec\\beta_n\\rangle$
is a basis of $V$ and the images $h(\\vec\\beta_1), \\dots, h(\\vec\\beta_n)$ are linearly
independent, then $h$ is one-to-one.

Here `B : Module.Basis (Fin n) ℝ V` is a basis of $V$; `B.repr v i` is the $i$-th coordinate
of $\\vec v$ and `B.sum_repr v : ∑ i, B.repr v i • B i = v`. Your `inj_iff_kernel` reduces
one-to-one to a trivial null space. `simp only [map_smul] at h` pushes $h$ through every term
of a sum (`rw` cannot rewrite inside a `∑`).
"

namespace LinearAlgebraGame

/-- If $h$ sends a basis to an independent sequence, then $h$ is one-to-one. -/
Statement inj_of_indep_images {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] {n : ℕ} (B : Module.Basis (Fin n) ℝ V) (h : V →ₗ[ℝ] W)
    (hli : LinearIndependent ℝ (fun i => h (B i))) : Function.Injective h := by
  Hint "Show the null space is trivial: if $h(c_1\\vec\\beta_1+\\dots+c_n\\vec\\beta_n) = \\vec 0$ then
  $c_1 h(\\vec\\beta_1)+\\dots+c_n h(\\vec\\beta_n) = \\vec 0$, so all $c_i = 0$."
  Hint (hidden := true) "`rw [inj_iff_kernel]`, then `intro v hv`."
  rw [inj_iff_kernel]
  intro v hv
  Hint "Write $\\vec v$ in coordinates and push $h$ inside the sum."
  Hint (hidden := true) "`rw [← B.sum_repr v, map_sum] at {hv}`, then `simp only [map_smul] at {hv}`."
  rw [← B.sum_repr v, map_sum] at hv
  simp only [map_smul] at hv
  Hint "Now `{hv}` is a relation among the images. Independence makes every coordinate zero."
  Hint (hidden := true) "`have hc := Fintype.linearIndependent_iff.mp {hli} _ {hv}`"
  have hc := Fintype.linearIndependent_iff.mp hli _ hv
  Hint (hidden := true) "`rw [← B.sum_repr v]` and `simp only [{hc}, zero_smul, Finset.sum_const_zero]`."
  rw [← B.sum_repr v]
  simp only [hc, zero_smul, Finset.sum_const_zero]

end LinearAlgebraGame

Conclusion "
`inj_of_indep_images` is in your inventory — that is (5) ⇒ (1) of the boss.
"

NewTheorem LinearAlgebraGame.inj_iff_kernel Finset.sum_const_zero
DisabledTactic norm_num
TheoremTab "Dimension"
