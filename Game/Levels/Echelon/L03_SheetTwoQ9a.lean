import Game.Levels.Echelon.L02_ElementaryMatrix

World "Echelon"
Level 3
Title "Column relations, one row operation"

-- @sheet 2 Q9a
/-! @answer
After $k\rho_1 + \rho_2$ the matrix is
$\begin{pmatrix}1&2&3\\k+3&2k&3k+3\\1&4&5\end{pmatrix}$, and in each row the first two
entries still add to the third: $1+2 = 3$, $(k+3) + 2k = 3k+3$, $1 + 4 = 5$.
-/
Introduction "
**Problem Sheet 2, Question 9(a).** In the matrix
$B = \\begin{pmatrix}1&2&3\\\\3&0&3\\\\1&4&5\\end{pmatrix}$ the first and second columns add to
the third. This remains true under any row operation. Show it for $k\\rho_1 + \\rho_2$.

The result of the row operation is the matrix $C$ = `combo 0 1 k * B`; the claim is that in
every row $i$ of $C$, entry 0 + entry 1 = entry 2.
"

namespace LinearAlgebraGame

open Matrix in
/-- After $k\rho_1 + \rho_2$, column 1 + column 2 = column 3 still. -/
Statement (k : ℝ) (C : Matrix (Fin 3) (Fin 3) ℝ)
    (hC : C = combo 0 1 k * !![1, 2, 3; 3, 0, 3; 1, 4, 5]) :
    ∀ i, C i 0 + C i 1 = C i 2 := by
  intro i
  rw [hC]
  Hint "Check each row."
  Hint (hidden := true) "`fin_cases i <;> simp [combo, Matrix.add_mul, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply] <;> ring`"
  fin_cases i <;> simp [combo, Matrix.add_mul, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply] <;> ring

end LinearAlgebraGame

Conclusion "Row 2 became $(k+3,\\ 2k,\\ 3k+3)$, and $(k+3) + 2k = 3k + 3$."
