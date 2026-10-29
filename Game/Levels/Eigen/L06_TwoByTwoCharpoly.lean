import Game.Levels.Eigen.L05_EigenDet

World "Eigen"
Level 6
Title "The characteristic polynomial of a 2×2 matrix"

Introduction "
**Definition Five.II.3.9.** The *characteristic polynomial* of $T$ is $|T - xI|$. In Lean it is
`charpolyH T`, defined as the determinant of `C.mapMatrix T - scalar (Fin 2) X`: the matrix
$T$ with its entries viewed as constant polynomials, minus $x I$. Here `X` is the variable
$x$ and `C a` is the constant polynomial $a$.

Every $2\\times2$ matrix has the same shape of characteristic polynomial:
$$\\begin{vmatrix} a - x & b \\\\ c & d - x\\end{vmatrix} = x^2 - (a + d)\\,x + (ad - bc),$$
the trace and the determinant. **Prove it** once; afterwards every $2 \\times 2$
characteristic polynomial is one `rw` away.

*Typing constants:* a real number $r$ inside a polynomial is `C r`. `C` respects arithmetic:
`Polynomial.C_add : C (a + b) = C a + C b`, and likewise `C_sub`, `C_mul`.
"

namespace LinearAlgebraGame

open Polynomial in
/-- $|T - xI| = x^2 - (a+d)x + (ad - bc)$ for $T = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$. -/
Statement charpolyH_two (a b c d : ℝ) :
    charpolyH !![a, b; c, d] = X ^ 2 - C (a + d) * X + C (a * d - b * c) := by
  Hint "Write $T - xI$ as an explicit $2\\times2$ matrix of polynomials, take its determinant
  with the $ad - bc$ formula, and compare."
  Hint (hidden := true) "`rw [charpolyH]`, then
  `have e : … = !![C a - X, C b; C c, C d - X] := by entrywise <;> simp`."
  rw [charpolyH]
  have e : ((C : ℝ →+* ℝ[X]).mapMatrix !![a, b; c, d] - Matrix.scalar (Fin 2) (X : ℝ[X]))
      = !![C a - X, C b; C c, C d - X] := by
    entrywise <;> simp
  Hint (hidden := true) "`rw [e, Matrix.det_fin_two_of, C_add, C_sub, C_mul, C_mul]`, then `ring`."
  rw [e, Matrix.det_fin_two_of, C_add, C_sub, C_mul, C_mul]
  ring

end LinearAlgebraGame

Conclusion "
The coefficients are the trace $a + d$ and the determinant $ad - bc$ — both unchanged under
similarity, as they must be.
"

NewDefinition LinearAlgebraGame.charpolyH
NewTheorem Polynomial.C_add Polynomial.C_sub Polynomial.C_mul
TheoremTab "Eigen"
