import Game.Levels.Diagonalisation.L03_Sum

World "Diagonalisation"
Level 4
Title "What about composition?"

-- @sheet 10 Q2c
/-! @answer
**Not necessarily.** $T = \begin{pmatrix}1&1\\0&0\end{pmatrix}$ is diagonalisable (distinct
eigenvalues), $S = \begin{pmatrix}0&0\\0&1\end{pmatrix}$ is diagonal, but
$TS = \begin{pmatrix}0&1\\0&0\end{pmatrix}$ is nonzero with square zero, hence not diagonalisable.
-/
Introduction "
**Problem Sheet 10, Question 2** (third part). If $t$ and $s$ are diagonalisable, is
$t \\circ s$? (In matrices, $t\\circ s$ is the product $TS$.)

*Decide level.*
"

namespace LinearAlgebraGame

open Matrix in
/-- True or false: the product of two diagonalisable matrices is diagonalisable. -/
Statement :
    (¬ ∀ (n : ℕ) (T S : Matrix (Fin n) (Fin n) ℝ),
        Diagonalizable T → Diagonalizable S → Diagonalizable (T * S)) ∨
      (∀ (n : ℕ) (T S : Matrix (Fin n) (Fin n) ℝ),
        Diagonalizable T → Diagonalizable S → Diagonalizable (T * S)) := by
  Hint (hidden := true) "The same trick as for sums: aim for a nonzero product with square zero."
  Hint "Can you prove it in general, or is there a small counterexample? Decide, then commit."
  left
  intro h
  Hint (hidden := true) "Try T = !![1, 1; 0, 0] again and S = !![0, 0; 0, 1]."
  have hT : Diagonalizable (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    use ![1, 0]
    apply matSimilar_of_mul_eq_one (P := !![1, 1; 0, -1]) (Q := !![1, 1; 0, -1])
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hS : Diagonalizable (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    use ![0, 1]
    apply matSimilar_of_mul_eq_one (P := 1) (Q := 1)
    · rw [Matrix.one_mul]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hTS := h 2 _ _ hT hS
  have e : (!![1, 1; 0, 0] * !![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e] at hTS
  apply not_diagonalizable_of_sq_eq_zero _ _ _ hTS
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h0
    have := congrFun (congrFun h0 0) 1
    simp at this

end LinearAlgebraGame

Conclusion "**Not necessarily.** (It *is* true when $t$ and $s$ commute: then they can be diagonalised by a common basis.)"

TheoremTab "Eigen"
