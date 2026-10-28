import Game.Levels.ChangeOfBasis.L03_ArrowDiagram

World "ChangeOfBasis"
Level 4
Title "A representation is unique"

Introduction "
If $D$ is linearly independent, a map has only one representation with respect to $B, D$:
two candidate matrices $H, H'$ give
$\\sum_i (h_{ij} - h'_{ij})\\vec\\delta_i = h(\\vec\\beta_j) - h(\\vec\\beta_j) = \\vec 0$, so all the
coefficients vanish. This is what makes \"*the* matrix of a map\" meaningful.
"

namespace LinearAlgebraGame

/-- If $D$ is independent, $\mathrm{Rep}_{B,D}(h)$ is unique. -/
Statement isRep_unique {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] {m n : ℕ} {B : Fin n → V} {D : Fin m → W} {h : V →ₗ[ℝ] W}
    {H H' : Matrix (Fin m) (Fin n) ℝ} (hD : LinearIndependent ℝ D) (hH : IsRep B D h H)
    (hH' : IsRep B D h H') : H = H' := by
  ext i j
  Hint "Find a vanishing combination of the $\\vec\\delta$'s."
  Hint (hidden := true) "`have key : ∑ l, (H l j - H' l j) • D l = 0`, proved by
  `simp only [sub_smul, Finset.sum_sub_distrib]` and `rw [← {hH} j, ← {hH'} j, sub_self]`."
  have key : ∑ l, (H l j - H' l j) • D l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hH j, ← hH' j, sub_self]
  Hint (hidden := true) "`have := Fintype.linearIndependent_iff.mp {hD} _ key i`, then `linarith`."
  have := Fintype.linearIndependent_iff.mp hD _ key i
  linarith

end LinearAlgebraGame

Conclusion "
`isRep_unique` is in your inventory: to show two matrices are equal, show they represent the
same map with respect to the same bases.
"

TheoremTab "Change of basis"
