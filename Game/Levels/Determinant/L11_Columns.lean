import Game.Levels.Determinant.L10_EvalDet

World "Determinant"
Level 11
Title "Columns too"

Introduction "
**Theorem Four.I.3.15:** $\\det T^{\\mathsf T} = \\det T$ (`Matrix.det_transpose`). So every
statement about rows has a column version (Corollary 3.16). Transposing respects the
algebra: `Matrix.transpose_sub`, `Matrix.transpose_smul`, `Matrix.transpose_one` (in the
inventory from now on).

**Prove:** if two columns of $M$ are equal, then $\\det M = 0$.
"

namespace LinearAlgebraGame

/-- If columns $i \ne j$ of $M$ are equal then $\det M = 0$. -/
Statement {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (hij : i ≠ j)
    (h : ∀ k, M k i = M k j) : M.det = 0 := by
  Hint "Idea: transpose. Equal columns of $M$ are equal rows of the transpose of $M$, and you
  proved the row version for any determinant function — including `Matrix.det`."
  Hint (hidden := true) "`rw [← Matrix.det_transpose]`."
  rw [← Matrix.det_transpose]
  Hint (hidden := true) "`exact det_eq_zero_of_rows_eq _ detAxioms_det M.transpose i j hij (funext h)`."
  exact det_eq_zero_of_rows_eq _ detAxioms_det M.transpose i j hij (funext h)

end LinearAlgebraGame

Conclusion "Lemma 2.4 and the four conditions all hold for columns as well."

NewTheorem Matrix.det_transpose LinearAlgebraGame.det_eq_zero_of_rows_eq LinearAlgebraGame.detAxioms_det Matrix.transpose_sub Matrix.transpose_smul
DisabledTheorem Matrix.det_zero_of_column_eq
TheoremTab "Det"
