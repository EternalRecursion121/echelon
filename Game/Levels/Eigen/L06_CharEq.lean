import Game.Levels.Eigen.L05_EigenDet

World "Eigen"
Level 6
Title "The characteristic equation"

-- @sheet 9 Q7a
/-! @answer
$|T - xI| = \begin{vmatrix} 3-x & 2\\ -1 & -x\end{vmatrix} = (3-x)(-x) + 2 = x^2 - 3x + 2 = (x-1)(x-2)$,
so the characteristic equation is $x^2 - 3x + 2 = 0$ and the eigenvalues are exactly
$\lambda = 1$ and $\lambda = 2$.
-/
Introduction "
**Problem Sheet 9, Question 7** (part 1 of 3). Find the characteristic equation and the
eigenvalues of $T = \\begin{pmatrix} 3 & 2 \\\\ -1 & 0\\end{pmatrix}$.

`charpolyH T` is Hefferon's characteristic polynomial $|T - xI|$ (Def Five.II.3.9),
defined as the determinant of `C.mapMatrix T - scalar (Fin 2) X`: the matrix $T$ with
entries viewed as constant polynomials, minus $x I$. Here `X` is the variable $x$ and
`C a` the constant polynomial $a$.

**Prove both:** $|T - xI| = (x-1)(x-2)$, and the eigenvalues are exactly $1$ and $2$.
"

namespace LinearAlgebraGame

open Polynomial in
/-- $|T - xI| = (x-1)(x-2)$, and the eigenvalues of $T$ are exactly $1$ and $2$. -/
Statement sheet9_q7a :
    charpolyH (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = (X - C 1) * (X - C 2) ∧
    ∀ μ : ℝ, IsEigenvalue (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) μ ↔ μ = 1 ∨ μ = 2 := by
  Hint "Two parts: the polynomial, then its roots."
  constructor
  · Hint (hidden := true) "`rw [charpolyH]`, then identify the matrix:
    `have e : … = !![C 3 - X, C 2; -C 1, -X] := by entrywise <;> simp`."
    rw [charpolyH]
    have e : ((C : ℝ →+* ℝ[X]).mapMatrix !![3, 2; -1, 0] - Matrix.scalar (Fin 2) (X : ℝ[X]))
        = !![C 3 - X, C 2; -C 1, -X] := by
      entrywise <;> simp
    Hint (hidden := true) "`rw [e, Matrix.det_fin_two_of]`. To finish, you need `C 3 = C 1 + C 2`
    (prove it with `rw [← C_add]; norm_num`), then `linear_combination`."
    rw [e, Matrix.det_fin_two_of]
    have h3 : (C 3 : ℝ[X]) = C 1 + C 2 := by
      rw [← C_add]
      norm_num
    linear_combination (-X) * h3
  · intro μ
    Hint (hidden := true) "`rw [isEigenvalue_iff_det]`; then compute `T - μ • 1` as a
    `!![…]` matrix and use `Matrix.det_fin_two_of`."
    rw [isEigenvalue_iff_det]
    have e : (!![3, 2; -1, 0] - μ • 1 : Matrix (Fin 2) (Fin 2) ℝ) = !![3 - μ, 2; -1, -μ] := by
      entrywise <;> simp
    rw [e, Matrix.det_fin_two_of]
    constructor
    · intro h
      Hint (hidden := true) "Factor: `have h2 : (μ - 1) * (μ - 2) = 0 := by linarith`, then
      `mul_eq_zero`."
      have h2 : (μ - 1) * (μ - 2) = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h1 | h1
      · left
        linarith
      · right
        linarith
    · intro h
      rcases h with h | h
      · rw [h]
        norm_num
      · rw [h]
        norm_num

end LinearAlgebraGame

Conclusion "Characteristic equation $x^2 - 3x + 2 = 0$; eigenvalues $1$ and $2$."

NewDefinition LinearAlgebraGame.charpolyH
TheoremTab "Eigen"
NewTheorem Polynomial.C_add LinearAlgebraGame.charpolyH_eval LinearAlgebraGame.isEigenvalue_iff_det
