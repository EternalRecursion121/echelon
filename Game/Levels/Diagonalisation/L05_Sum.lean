import Game.Levels.Diagonalisation.L04_ScalarMultiple

World "Diagonalisation"
Level 5
Title "What about sums?"

-- @sheet 10 Q2b
/-! @answer
**Not necessarily.** $T = \begin{pmatrix}1&1\\0&0\end{pmatrix}$ has distinct eigenvalues $1, 0$
so is diagonalisable (eigenvectors $(1,0)$, $(1,-1)$), and $S = \begin{pmatrix}-1&0\\0&0\end{pmatrix}$
is already diagonal. But $T + S = \begin{pmatrix}0&1\\0&0\end{pmatrix}$ is nonzero with
$(T+S)^2 = 0$, so it is not diagonalisable.
-/
Introduction "
**Problem Sheet 10, Question 2** (second part). If $t$ and $s$ are diagonalisable, is
$t + s$?

*Decide level:* commit with `left` (no) or `right` (yes), then prove it.
"

namespace LinearAlgebraGame

open Matrix in
/-- True or false: the sum of two diagonalisable matrices is diagonalisable. -/
Statement :
    (¬ ∀ (n : ℕ) (T S : Matrix (Fin n) (Fin n) ℝ),
        Diagonalizable T → Diagonalizable S → Diagonalizable (T + S)) ∨
      (∀ (n : ℕ) (T S : Matrix (Fin n) (Fin n) ℝ),
        Diagonalizable T → Diagonalizable S → Diagonalizable (T + S)) := by
  Hint (hidden := true) "Look for two diagonalisable $2\\times2$ matrices adding up to a nonzero matrix with square zero."
  Hint "Can you prove it in general, or is there a small counterexample? Decide, then commit."
  left
  intro h
  Hint "Refute it with a pair of diagonalisable matrices whose sum is not diagonalisable. Which
  non-diagonalisable matrices do you know?"
  Hint (hidden := true) "Try T = !![1, 1; 0, 0] and S = !![-1, 0; 0, 0]: the sum is
  !![0, 1; 0, 0], nonzero with square zero (your first level of this world)."
  Hint (hidden := true) "Each of these $2\\times2$ matrices has two distinct eigenvalues, so
  `diagonalizable_of_two_eigenvalues` applies. An eigenvalue check is
  `rw [isEigenvalue_iff_det, ← charpolyH_eval, charpolyH_two]` followed by `norm_num`."
  have hT : Diagonalizable (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    apply diagonalizable_of_two_eigenvalues _ 1 0 _ _ (by norm_num) <;>
      rw [isEigenvalue_iff_det, ← charpolyH_eval, charpolyH_two] <;> norm_num
  have hS : Diagonalizable (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    apply diagonalizable_of_two_eigenvalues _ (-1) 0 _ _ (by norm_num) <;>
      rw [isEigenvalue_iff_det, ← charpolyH_eval, charpolyH_two] <;> norm_num
  have hTS := h 2 _ _ hT hS
  have e : (!![1, 1; 0, 0] + !![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 0, 0] := by
    entrywise <;> simp
  rw [e] at hTS
  Hint (hidden := true) "`apply not_diagonalizable_of_sq_eq_zero _ _ _ hTS` leaves the two facts to check."
  apply not_diagonalizable_of_sq_eq_zero _ _ _ hTS
  · entrywise <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h0
    have := congrFun (congrFun h0 0) 1
    simp at this

end LinearAlgebraGame

Conclusion "**Not necessarily**: two diagonalisable matrices can add up to a nilpotent one."

TheoremTab "Eigen"
