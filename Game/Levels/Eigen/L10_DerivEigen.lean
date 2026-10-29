import Game.Levels.Eigen.L09_DerivMatrix

World "Eigen"
Level 10
Title "Eigenvalues of d/dx"

-- @sheet 9 Q8a
/-! @answer
With respect to $\langle 1, x, x^2, x^3\rangle$, $d/dx$ has the strictly upper triangular
matrix $D$ with superdiagonal $1, 2, 3$. So $|D - xI| = (-x)^4 = x^4$, and the only
eigenvalue is $\lambda = 0$. The eigenspace $V_0$ is the kernel of $d/dx$: $p' = 0$ iff
$a_1 = 2a_2 = 3a_3 = 0$, i.e. $V_0 = \{a_0\}$ = the constant polynomials $= [\{1\}]$.
-/
Introduction "
**Problem Sheet 9, Question 8** (part 1 of 2). Find the eigenvalues and associated
eigenspaces of the differentiation operator $d/dx\\colon \\mathcal P_3 \\to \\mathcal P_3$.

**Prove:** (1) $\\lambda$ is an eigenvalue of $d/dx$ iff $\\lambda = 0$; (2) the eigenspace $V_0$
is the span of the constant polynomial $1$ (coefficient vector $(1,0,0,0)$).
"

namespace LinearAlgebraGame

/-- The only eigenvalue of $d/dx$ on $\mathcal P_3$ is $0$, with eigenspace the constants. -/
Statement sheet9_q8a :
    (∀ μ : ℝ, (∃ p : Poly 3, p ≠ 0 ∧ Poly.deriv p = μ • p) ↔ μ = 0) ∧
    Module.End.eigenspace (Poly.deriv : Poly 3 →ₗ[ℝ] Poly 3) 0 = Submodule.span ℝ {![1, 0, 0, 0]} := by
  Hint "Use the matrix $D$: the eigenvalues are the roots of $|D - xI|$."
  constructor
  · intro μ
    Hint (hidden := true) "`simp only [deriv_eq_mulVec]` turns the left side into
    `IsEigenvalue D μ` (unfolded); then `rw [← IsEigenvalue, isEigenvalue_iff_det]`."
    simp only [deriv_eq_mulVec]
    rw [← IsEigenvalue, isEigenvalue_iff_det]
    Hint (hidden := true) "Write `D - μ • 1` as a `!![…]` matrix (`entrywise <;> simp`),
    then `eval_det`."
    have e : (!![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0] - μ • 1 : Matrix (Fin 4) (Fin 4) ℝ)
        = !![-μ, 1, 0, 0; 0, -μ, 2, 0; 0, 0, -μ, 3; 0, 0, 0, -μ] := by
      entrywise <;> simp
    rw [e]
    eval_det
    Hint (hidden := true) "`pow_eq_zero_iff` (with `(by norm_num)`)."
    exact pow_eq_zero_iff (by norm_num)
  · Hint (hidden := true) "`ext p`, then
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

end LinearAlgebraGame

Conclusion "Only eigenvalue $0$; eigenspace = the constant polynomials."

NewTheorem LinearAlgebraGame.deriv_eq_mulVec pow_eq_zero_iff
TheoremTab "Eigen"
