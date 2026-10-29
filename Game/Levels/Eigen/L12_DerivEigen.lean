import Game.Levels.Eigen.L11_DerivCharpoly

World "Eigen"
Level 12
Title "Eigenvalues of d/dx"

-- @sheet 9 Q8b
/-! @answer
With respect to $\langle 1, x, x^2, x^3\rangle$, $d/dx$ has the strictly upper triangular
matrix $D$ with superdiagonal $1, 2, 3$. So $|D - xI| = (-x)^4 = x^4$, and the only
eigenvalue is $\lambda = 0$. The eigenspace $V_0$ is the kernel of $d/dx$: $p' = 0$ iff
$a_1 = 2a_2 = 3a_3 = 0$, i.e. $V_0 = \{a_0\}$ = the constant polynomials $= [\{1\}]$.
Its dimension, the geometric multiplicity of $0$, is $1$.
-/
Introduction "
**Problem Sheet 9, Question 8** (part 2 of 2). Find the eigenvalues and associated
eigenspaces of the differentiation operator $d/dx\\colon \\mathcal P_3 \\to \\mathcal P_3$.

**Find** $\\lambda_0$ such that $\\lambda$ is an eigenvalue of $d/dx$ iff $\\lambda = \\lambda_0$,
and a polynomial $p_0 \\ne 0$ spanning the eigenspace $V_{\\lambda_0}$; then the geometric
multiplicity $\\dim V_{\\lambda_0}$ is $1$.

Here $d/dx$ is an operator on `Poly 3`, so \"$\\lambda$ is an eigenvalue\" is spelled out:
`∃ p ≠ 0, Poly.deriv p = λ • p`. Rewriting `Poly.deriv p` as `D *ᵥ p` (your level
`deriv_eq_mulVec`, with `simp only` since it sits under `∃`) turns this into exactly the
definition of `IsEigenvalue D λ`, and `rw [← IsEigenvalue]` folds it up. The eigenspace of
`Poly.deriv` is unfolded with `Module.End.mem_eigenspace_iff : v ∈ eigenspace f μ ↔ f v = μ • v`.
"

namespace LinearAlgebraGame

open Polynomial in
/-- $d/dx$ on $\mathcal P_3$ has exactly one eigenvalue $\lambda_0$; its eigenspace is spanned by one nonzero polynomial, so it has dimension $1$. -/
Statement : ∃ μ₀ : ℝ, (∀ μ : ℝ, (∃ p : Poly 3, p ≠ 0 ∧ Poly.deriv p = μ • p) ↔ μ = μ₀) ∧
    ∃ p₀ : Poly 3, p₀ ≠ 0 ∧
      Module.End.eigenspace (Poly.deriv : Poly 3 →ₗ[ℝ] Poly 3) μ₀ = Submodule.span ℝ {p₀} ∧
      Module.finrank ℝ (Module.End.eigenspace (Poly.deriv : Poly 3 →ₗ[ℝ] Poly 3) μ₀) = 1 := by
  Hint "The eigenvalues are the roots of $|D - xI|$, which you computed. The eigenspace of
  the root is the kernel of $d/dx$."
  Hint (hidden := true) "`use 0` and `constructor`."
  use 0
  constructor
  · intro μ
    Hint (hidden := true) "`simp only [deriv_eq_mulVec]`, `rw [← IsEigenvalue, isEigenvalue_iff_det, ← charpolyH_eval, deriv_charpoly.1, eval_pow, eval_X]`,
    then `pow_eq_zero_iff` (with `(by norm_num)`)."
    simp only [deriv_eq_mulVec]
    rw [← IsEigenvalue, isEigenvalue_iff_det, ← charpolyH_eval, deriv_charpoly.1, eval_pow, eval_X]
    exact pow_eq_zero_iff (by norm_num)
  · Hint (hidden := true) "The constants: `use ![1, 0, 0, 0]`."
    use ![1, 0, 0, 0]
    have hne : (![1, 0, 0, 0] : Poly 3) ≠ 0 := by simp
    have hV : Module.End.eigenspace (Poly.deriv : Poly 3 →ₗ[ℝ] Poly 3) 0
        = Submodule.span ℝ {![1, 0, 0, 0]} := by
      Hint (hidden := true) "`ext p`, then
      `rw [Module.End.mem_eigenspace_iff, deriv_eq_mulVec, zero_smul, Submodule.mem_span_singleton]`."
      ext p
      rw [Module.End.mem_eigenspace_iff, deriv_eq_mulVec, zero_smul, Submodule.mem_span_singleton]
      constructor
      · intro h
        Hint (hidden := true) "`use p 0`; the coordinate equations `congrFun h 0`, `congrFun h 1`,
        `congrFun h 2` say $a_1 = 2a_2 = 3a_3 = 0$."
        use p 0
        have h0 := congrFun h 0
        have h1 := congrFun h 1
        have h2 := congrFun h 2
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0 h1 h2
        entrywise <;> simp [h0, h1, h2]
      · intro h
        obtain ⟨a, ha⟩ := h
        rw [← ha]
        entrywise <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    Hint (hidden := true) "`rw [hV]` and `finrank_span_singleton hne`."
    exact ⟨hne, hV, by rw [hV]; exact finrank_span_singleton hne⟩

end LinearAlgebraGame

Conclusion "Only eigenvalue $0$; eigenspace = the constant polynomials, a line: geometric multiplicity $1$ against algebraic multiplicity $4$."

NewTheorem LinearAlgebraGame.deriv_eq_mulVec LinearAlgebraGame.deriv_charpoly pow_eq_zero_iff Polynomial.eval_pow Module.End.mem_eigenspace_iff
TheoremTab "Eigen"
