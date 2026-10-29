import Game.Levels.Eigen.L06_TwoByTwoCharpoly

World "Eigen"
Level 7
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

**Find** numbers $a, b$ with $|T - xI| = (x - a)(x - b)$, and show that the eigenvalues of
$T$ are exactly $a$ and $b$.

Tools: `charpolyH_two` (your last level), `X_sub_C_mul_X_sub_C` multiplies out
$(x-a)(x-b) = x^2 - (a+b)x + ab$ (after which `norm_num` can compare the numbers), and
`charpolyH_eval : (charpolyH T).eval μ = (T - μ • 1).det` links the polynomial to
`isEigenvalue_iff_det`. A polynomial is evaluated with `Polynomial.eval_mul`, `eval_sub`,
`eval_X`, `eval_C`.
"

namespace LinearAlgebraGame

open Polynomial in
/-- There are $a, b$ with $|T - xI| = (x-a)(x-b)$, and the eigenvalues of $T$ are exactly $a$ and $b$. -/
Statement sheet9_q7a :
    ∃ a b : ℝ, charpolyH (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = (X - C a) * (X - C b) ∧
      ∀ μ : ℝ, IsEigenvalue (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) μ ↔ μ = a ∨ μ = b := by
  Hint "Compute $|T - xI|$ with the $2\\times2$ formula and factor it. Then: $\\mu$ is an
  eigenvalue iff $|T - \\mu I| = 0$, and that is the polynomial evaluated at $\\mu$."
  Hint (hidden := true) "$x^2 - 3x + 2 = (x - 1)(x - 2)$: `use 1, 2`."
  use 1, 2
  Hint (hidden := true) "Prove the factorisation first:
  `have hc : charpolyH !![3, 2; -1, 0] = (X - C 1) * (X - C 2) := by rw [charpolyH_two, X_sub_C_mul_X_sub_C]; norm_num`."
  have hc : charpolyH (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = (X - C 1) * (X - C 2) := by
    rw [charpolyH_two, X_sub_C_mul_X_sub_C]
    norm_num
  constructor
  · exact hc
  · intro μ
    Hint (hidden := true) "`rw [isEigenvalue_iff_det, ← charpolyH_eval, hc]`, then evaluate:
    `eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C`, and finish with
    `mul_eq_zero, sub_eq_zero, sub_eq_zero`."
    rw [isEigenvalue_iff_det, ← charpolyH_eval, hc, eval_mul, eval_sub, eval_sub, eval_X, eval_C,
      eval_C, mul_eq_zero, sub_eq_zero, sub_eq_zero]

end LinearAlgebraGame

Conclusion "Characteristic equation $x^2 - 3x + 2 = 0$; eigenvalues exactly $1$ and $2$."

TheoremTab "Eigen"
NewTheorem LinearAlgebraGame.charpolyH_two LinearAlgebraGame.X_sub_C_mul_X_sub_C LinearAlgebraGame.charpolyH_eval LinearAlgebraGame.isEigenvalue_iff_det Polynomial.eval_mul Polynomial.eval_sub Polynomial.eval_X Polynomial.eval_C
