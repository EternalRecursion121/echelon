import Game.Levels.Eigen.L10_DerivEigen

World "Eigen"
Level 11
Title "Multiplicities of d/dx"

-- @sheet 9 Q8b
/-! @answer
$|D - xI| = x^4$, so $\lambda = 0$ has algebraic multiplicity $4$. Its eigenspace is the
constants, a line, so the geometric multiplicity is $1$. (So $d/dx$ is not diagonalisable.)
-/
Introduction "
**Problem Sheet 9, Question 8** (part 2 of 2). State the algebraic and geometric
multiplicities of the eigenvalues of $d/dx$ on $\\mathcal P_3$.

**Prove:** $|D - xI| = x^4$, so $0$ has algebraic multiplicity $4$; and $\\dim V_0 = 1$.
"

namespace LinearAlgebraGame

open Polynomial in
/-- $|D - xI| = x^4$; the eigenvalue $0$ has algebraic multiplicity $4$ and geometric multiplicity $1$. -/
Statement :
    charpolyH (!![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℝ) = X ^ 4 ∧
    rootMultiplicity 0 (charpolyH (!![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) ℝ)) = 4 ∧
    Module.finrank ℝ (Module.End.eigenspace (Poly.deriv : Poly 3 →ₗ[ℝ] Poly 3) 0) = 1 := by
  Hint "First compute the characteristic polynomial; the rest follows from it and from the
  eigenspace you found."
  have hc : charpolyH (!![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) ℝ) = X ^ 4 := by
    Hint (hidden := true) "`rw [charpolyH]`, write the polynomial matrix as a `!![…]` literal
    (entries `-X`, `1`, `C 2`, `C 3`, `0`), then `eval_det`."
    rw [charpolyH]
    have e : ((C : ℝ →+* ℝ[X]).mapMatrix !![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0]
        - Matrix.scalar (Fin 4) (X : ℝ[X]))
        = !![-X, 1, 0, 0; 0, -X, C 2, 0; 0, 0, -X, C 3; 0, 0, 0, -X] := by
      entrywise <;> simp
    rw [e]
    eval_det
  refine ⟨hc, ?_, ?_⟩
  · Hint (hidden := true) "`rw [hc, ← sub_zero X, ← C_0, rootMultiplicity_X_sub_C_pow]`."
    rw [hc, ← sub_zero X, ← C_0, rootMultiplicity_X_sub_C_pow]
  · Hint (hidden := true) "`rw [sheet9_q8a.2]`, then `finrank_span_singleton`."
    rw [sheet9_q8a.2]
    apply finrank_span_singleton
    intro h
    have := congrFun h 0
    simp at this

end LinearAlgebraGame

Conclusion "Algebraic multiplicity $4$, geometric $1$: as unequal as possible."

NewTheorem LinearAlgebraGame.sheet9_q8a Polynomial.rootMultiplicity_X_sub_C_pow Polynomial.C_0
TheoremTab "Eigen"
