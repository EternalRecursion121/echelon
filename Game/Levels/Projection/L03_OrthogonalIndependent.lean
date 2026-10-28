import Game.Levels.Projection.L02_ProjShorter

World "Projection"
Level 3
Title "Orthogonal vectors are independent"

Introduction "
Hefferon Theorem Three.VI.2.2: mutually orthogonal nonzero vectors are linearly independent.

Proof: if $c_1\\vec v_1 + \\dots + c_k\\vec v_k = \\vec 0$, dot both sides with $\\vec v_i$. Every
term but one vanishes, leaving $c_i(\\vec v_i\\cdot\\vec v_i) = 0$, and $\\vec v_i\\cdot\\vec v_i \\ne 0$.
"

namespace LinearAlgebraGame

open Matrix in
/-- Nonzero, mutually orthogonal vectors are linearly independent. -/
Statement linearIndependent_of_orthogonal {k n : ℕ} (v : Fin k → (Fin n → ℝ))
    (h0 : ∀ i, v i ≠ 0) (horth : ∀ i j, i ≠ j → v i ⬝ᵥ v j = 0) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  Hint "Dot the relation `{hg}` with $\\vec v_i$."
  Hint (hidden := true) "`have h := congrArg (fun w => w ⬝ᵥ v i) {hg}`, then
  `simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at h`."
  have h := congrArg (fun w => w ⬝ᵥ v i) hg
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at h
  Hint "Only the $i$-th term of the sum survives."
  Hint (hidden := true) "`rw [Finset.sum_eq_single i] at h`"
  rw [Finset.sum_eq_single i] at h
  · have hii : v i ⬝ᵥ v i ≠ 0 := fun e => h0 i (dotProduct_self_eq_zero.mp e)
    Hint (hidden := true) "`exact (mul_eq_zero.mp h).resolve_right hii`"
    exact (mul_eq_zero.mp h).resolve_right hii
  · intro j _ hj
    rw [horth j i hj, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end LinearAlgebraGame

Conclusion "
So $k$ nonzero orthogonal vectors in a $k$-dimensional space form a basis — an *orthogonal
basis*, in which coordinates are just $c_i = \\vec v\\cdot\\vec\\kappa_i / \\vec\\kappa_i\\cdot\\vec\\kappa_i$.
"

TheoremTab "Projection"
NewTheorem sum_dotProduct Finset.sum_eq_single Finset.mem_univ
