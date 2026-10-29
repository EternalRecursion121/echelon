import Game.Levels.Diagonalisation.L02_ScalarMultiple

World "Diagonalisation"
Level 3
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

*Decide level.* Tools: `matSimilar_of_mul_eq_one (hQP : Q * P = 1) (h : S = P * T * Q) : MatSimilar T S`
saves you from computing inverses, and your earlier results about diagonalisability are in the
inventory.
Concrete $2\\times2$ products can be checked entry by entry:
`entrywise <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
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
  Hint "Refute it with a pair of diagonalisable matrices whose sum is not diagonalisable. Your
  `not_diagonalizable_of_sq_eq_zero` recognises some non-diagonalisable matrices."
  Hint (hidden := true) "Try T = !![1, 1; 0, 0] (diagonalised by P = !![1, 1; 0, -1], which is
  its own inverse) and S = !![-1, 0; 0, 0]."
  have hT : Diagonalizable (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    use ![1, 0]
    apply matSimilar_of_mul_eq_one (P := !![1, 1; 0, -1]) (Q := !![1, 1; 0, -1])
    · entrywise <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · entrywise <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hS : Diagonalizable (!![-1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    use ![-1, 0]
    apply matSimilar_of_mul_eq_one (P := 1) (Q := 1)
    · rw [Matrix.one_mul]
    · entrywise <;> simp
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

NewTheorem LinearAlgebraGame.matSimilar_of_mul_eq_one LinearAlgebraGame.not_diagonalizable_of_sq_eq_zero
TheoremTab "Eigen"
