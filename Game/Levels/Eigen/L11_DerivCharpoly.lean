import Game.Levels.Eigen.L10_DerivMatrix

World "Eigen"
Level 11
Title "The characteristic polynomial of d/dx"

-- @sheet 9 Q8a
/-! @answer
With respect to $\langle 1, x, x^2, x^3\rangle$, $d/dx$ has the strictly upper triangular
matrix $D$ with superdiagonal $1, 2, 3$, so $|D - xI| = (-x)^4 = x^4$ (a triangular matrix:
product of the diagonal). The only eigenvalue is $\lambda = 0$, with **algebraic multiplicity
$4$**. Its eigenspace is the constants $[\{1\}]$, a line, so the **geometric multiplicity is
$1$** (next level). Algebraic $4 >$ geometric $1$, so $d/dx$ is not diagonalisable.
-/
Introduction "
**Problem Sheet 9, Question 8** (part 1 of 2). State the algebraic and geometric
multiplicities of the eigenvalues of the differentiation operator $d/dx$ on $\\mathcal P_3$.

Hefferon's method starts with the characteristic polynomial of the matrix $D$ of $d/dx$ from
the last level. **Prove:** $|D - xI| = x^4$, so $0$ has algebraic multiplicity $4$. (The
geometric multiplicity comes with the eigenspace, in the next level.)

`eval_det` also computes determinants of matrices of polynomials — once the matrix is
written as a `!![…]` literal. Inside such a literal write the constants as `C 2`, `C 3`
(a bare `2` would be read differently and the comparison gets stuck).
"

namespace LinearAlgebraGame

open Polynomial in
/-- $|D - xI| = x^4$, and the eigenvalue $0$ has algebraic multiplicity $4$. -/
Statement deriv_charpoly :
    charpolyH (!![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℝ) = X ^ 4 ∧
    rootMultiplicity 0 (charpolyH (!![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) ℝ)) = 4 := by
  Hint "First compute the characteristic polynomial: $D - xI$ is triangular. Then read off
  the multiplicity of the root $0$ of $x^4 = (x - 0)^4$."
  have hc : charpolyH (!![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) ℝ) = X ^ 4 := by
    Hint (hidden := true) "`rw [charpolyH]`, write the polynomial matrix as a `!![…]` literal
    (entries `-X`, `1`, `C 2`, `C 3`, `0`) with `entrywise <;> simp`, then `eval_det`."
    rw [charpolyH]
    have e : ((C : ℝ →+* ℝ[X]).mapMatrix !![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3; 0, 0, 0, 0]
        - Matrix.scalar (Fin 4) (X : ℝ[X]))
        = !![-X, 1, 0, 0; 0, -X, C 2, 0; 0, 0, -X, C 3; 0, 0, 0, -X] := by
      entrywise <;> simp
    rw [e]
    eval_det
  constructor
  · exact hc
  · Hint (hidden := true) "Make $x^4$ look like $(x - 0)^4$:
    `rw [hc, ← sub_zero X, ← C_0, rootMultiplicity_X_sub_C_pow]`."
    rw [hc, ← sub_zero X, ← C_0, rootMultiplicity_X_sub_C_pow]

end LinearAlgebraGame

Conclusion "Algebraic multiplicity $4$. Now: which polynomials are actually eigenvectors?"

NewTheorem Polynomial.rootMultiplicity_X_sub_C_pow Polynomial.C_0
TheoremTab "Eigen"
