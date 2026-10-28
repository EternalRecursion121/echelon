import Game.Levels.MatrixOfMap.L07_Bridge

World "MatrixOfMap"
Level 8
Title "Composition is the matrix product"

Introduction "
Theorem Three.IV.2.7: if $H$ represents $h : U \\to V$ (with respect to $B$, $C$) and $G$
represents $g : V \\to W$ (with respect to $C$, $D$), then $GH$ represents $g \\circ h$
(with respect to $B$, $D$). This is *why* matrix multiplication is defined the way it is.

The computation for column $j$:
$$g(h(\\vec\\beta_j)) = g\\Big(\\sum_l h_{lj}\\vec\\gamma_l\\Big) = \\sum_l h_{lj}\\sum_i g_{il}\\vec\\delta_i
= \\sum_i \\Big(\\sum_l g_{il}h_{lj}\\Big)\\vec\\delta_i .$$
"

namespace LinearAlgebraGame

/-- If $H = \mathrm{Rep}_{B,C}(h)$ and $G = \mathrm{Rep}_{C,D}(g)$ then
$GH = \mathrm{Rep}_{B,D}(g \circ h)$. -/
Statement isRep_comp {U V W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V]
    [Module ℝ V] [AddCommGroup W] [Module ℝ W] {k m n : ℕ} {B : Fin n → U} {C : Fin m → V}
    {D : Fin k → W} {h : U →ₗ[ℝ] V} {g : V →ₗ[ℝ] W} {H : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin k) (Fin m) ℝ} (hH : IsRep B C h H) (hG : IsRep C D g G) :
    IsRep B D (g ∘ₗ h) (G * H) := by
  intro j
  Hint "First apply $h$ to $\\vec\\beta_j$ using `{hH}`, and push $g$ through the sum."
  Hint (hidden := true) "`rw [LinearMap.comp_apply, {hH} j, map_sum]`"
  rw [LinearMap.comp_apply, hH j, map_sum]
  Hint "Now in two steps: first replace each $g(h_\{lj}\\vec\\gamma_l)$ by $h_\{lj}\\sum_i g_\{il}\\vec\\delta_i$,
  then reorganise the double sum."
  calc ∑ l, g (H l j • C l) = ∑ l, H l j • ∑ i, G i l • D i := by
        Hint (hidden := true) "Termwise: `apply Finset.sum_congr rfl`, `intro l _`,
        `rw [map_smul, {hG} l]`."
        apply Finset.sum_congr rfl
        intro l _
        rw [map_smul, hG l]
    _ = ∑ i, (G * H) i j • D i := by
        Hint (hidden := true) "`simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply,
        Finset.sum_smul]`, then swap the order of summation with `rw [Finset.sum_comm]`, and
        match terms with `Finset.sum_congr rfl` twice and `mul_comm`."
        simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_comm]

end LinearAlgebraGame

Conclusion "
Composition of maps is multiplication of their matrices. `isRep_comp` is now in your
inventory — it is the arrow diagram of Three.IV.2.
"

TheoremTab "Matrices"
NewTheorem Finset.sum_smul Finset.sum_comm Finset.sum_congr
