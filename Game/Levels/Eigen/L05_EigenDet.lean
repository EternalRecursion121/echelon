import Game.Levels.Eigen.L04_Polynomial

World "Eigen"
Level 5
Title "Eigenvalues are where the determinant vanishes"

Introduction "
**Definition Five.II.3.1.** $\\lambda$ is an *eigenvalue* of $T$ if $T\\vec\\zeta = \\lambda\\vec\\zeta$
for some $\\vec\\zeta \\ne \\vec 0$. In Lean: `IsEigenvalue T μ`.

The computational test (Hefferon's slides): $\\lambda$ is an eigenvalue $\\iff$ $T - \\lambda I$
is singular $\\iff$ $|T - \\lambda I| = 0$. From Chapter Three you have
`Matrix.exists_mulVec_eq_zero_iff : (∃ v ≠ 0, M *ᵥ v = 0) ↔ M.det = 0`.
"

namespace LinearAlgebraGame

open Matrix in
/-- $\lambda$ is an eigenvalue of $T$ iff $\det(T - \lambda I) = 0$. -/
Statement isEigenvalue_iff_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    IsEigenvalue T μ ↔ (T - μ • 1).det = 0 := by
  Hint "Idea: $T\\vec v = \\lambda\\vec v \\iff (T - \\lambda I)\\vec v = \\vec 0$."
  Hint (hidden := true) "`rw [← exists_mulVec_eq_zero_iff]`, then `constructor`."
  rw [← exists_mulVec_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨v, hv, hTv⟩ := h
    use v, hv
    Hint (hidden := true) "`rw [sub_mulVec, smul_mulVec, one_mulVec, hTv, sub_self]`."
    rw [sub_mulVec, smul_mulVec, one_mulVec, hTv, sub_self]
  · intro h
    obtain ⟨v, hv, hTv⟩ := h
    use v, hv
    Hint (hidden := true) "`rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hTv`."
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hTv
    exact hTv

end LinearAlgebraGame

Conclusion "
So the eigenvalues are the roots of the characteristic polynomial $|T - xI|$
(`charpolyH T`; `charpolyH_eval` says its value at $\\mu$ is $|T - \\mu I|$).
"

NewDefinition LinearAlgebraGame.IsEigenvalue
NewTheorem Matrix.exists_mulVec_eq_zero_iff Matrix.sub_mulVec Matrix.smul_mulVec
TheoremTab "Eigen"
