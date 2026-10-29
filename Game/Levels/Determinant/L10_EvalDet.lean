import Game.Levels.Determinant.L09_Vandermonde

World "Determinant"
Level 10
Title "A power tool"

Introduction "
You have computed determinants by hand. From now on you may let the machine do the
arithmetic: the tactic `eval_det` computes the determinant of any concrete `!![…]` matrix
(Mathlib runs a fraction-free Gaussian elimination and checks a certificate).

**Is this $4 \\times 4$ matrix singular?**
$$\\begin{pmatrix} 1&2&0&1\\\\ 0&1&3&0\\\\ 2&0&1&1\\\\ 1&1&1&2\\end{pmatrix}$$

*Decide level:* the goal is `(¬ P) ∨ P` with $P$ = \"the determinant is $0$\". Commit with
`left` (not singular) or `right` (singular), then prove it.
"

namespace LinearAlgebraGame

/-- True or false: this $4\times4$ matrix is singular ($\det = 0$). -/
Statement :
    (¬ (!![1, 2, 0, 1; 0, 1, 3, 0; 2, 0, 1, 1; 1, 1, 1, 2] : Matrix (Fin 4) (Fin 4) ℝ).det = 0) ∨
      (!![1, 2, 0, 1; 0, 1, 3, 0; 2, 0, 1, 1; 1, 1, 1, 2] : Matrix (Fin 4) (Fin 4) ℝ).det = 0 := by
  Hint "By hand this is $24$ terms of the permutation expansion. Is there a faster way to
  find the determinant? Find it first, then decide."
  Hint (hidden := true) "`eval_det` replaces the determinant by its value (wherever it occurs
  in the goal). Then commit, and finish the arithmetic with `norm_num`."
  left
  eval_det
  norm_num

end LinearAlgebraGame

Conclusion "**Not singular**: the determinant is $17$. (By hand that is 24 terms of the permutation expansion.)"

NewTactic eval_det
TheoremTab "Det"
