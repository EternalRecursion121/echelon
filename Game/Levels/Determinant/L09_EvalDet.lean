import Game.Levels.Determinant.L08_Vandermonde

World "Determinant"
Level 9
Title "A power tool"

Introduction "
You have computed determinants by hand. From now on you may let the machine do the
arithmetic: the tactic `eval_det` computes the determinant of any concrete `!![…]` matrix
(Mathlib runs a fraction-free Gaussian elimination and checks a certificate).

Is this $4 \\times 4$ matrix singular?
$$\\begin{pmatrix} 1&2&0&1\\\\ 0&1&3&0\\\\ 2&0&1&1\\\\ 1&1&1&2\\end{pmatrix}$$
"

namespace LinearAlgebraGame

/-- $\det\begin{pmatrix} 1&2&0&1\\ 0&1&3&0\\ 2&0&1&1\\ 1&1&1&2\end{pmatrix} = 17$. -/
Statement : (!![1, 2, 0, 1; 0, 1, 3, 0; 2, 0, 1, 1; 1, 1, 1, 2] : Matrix (Fin 4) (Fin 4) ℝ).det
    = 17 := by
  Hint (hidden := true) "`eval_det`."
  eval_det

end LinearAlgebraGame

Conclusion "Nonzero, so the matrix is nonsingular. (By hand that is 24 terms of the permutation expansion.)"

NewTactic eval_det
TheoremTab "Det"
