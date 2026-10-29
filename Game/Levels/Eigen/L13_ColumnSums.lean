import Game.Levels.Eigen.L12_RowSums

World "Eigen"
Level 13
Title "What about columns?"

-- @sheet 10 Q6b
/-! @answer
**Yes.** If each column of $A$ sums to $c$, then each row of $A^{\mathsf T}$ sums to $c$, so
$c$ is an eigenvalue of $A^{\mathsf T}$ and $|A^{\mathsf T} - cI| = 0$. But
$|A - cI| = |(A - cI)^{\mathsf T}| = |A^{\mathsf T} - cI| = 0$, so $c$ is an eigenvalue of $A$.
The eigenvector is in general *not* $(1,\dots,1)$ any more.
-/
Introduction "
**Problem Sheet 10, Question 6** (second part). Is the same true if instead each
*column* sums to $c$?

*Decide level:* the goal is `(¬ P) ∨ P`. Commit with `left` (no) or `right` (yes), then prove it.
"

namespace LinearAlgebraGame

open Matrix in
/-- True or false: if every column of $A$ sums to $c$ then $c$ is an eigenvalue of $A$. -/
Statement :
    (¬ ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ),
        (∀ j, ∑ i, A i j = c) → IsEigenvalue A c) ∨
      (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ),
        (∀ j, ∑ i, A i j = c) → IsEigenvalue A c) := by
  Hint "Decide first: try a small $2\\times 2$ example whose columns sum to $c$, and compare with
  the row-sum case."
  Hint (hidden := true) "Columns of $A$ are rows of the transpose. Do $A$ and its transpose have
  the same eigenvalues?"
  right
  intro n A c h
  Hint (hidden := true) "`rw [isEigenvalue_iff_det, ← det_transpose]`, then
  `rw [transpose_sub, transpose_smul, transpose_one, ← isEigenvalue_iff_det]`."
  rw [isEigenvalue_iff_det, ← det_transpose, transpose_sub, transpose_smul, transpose_one,
    ← isEigenvalue_iff_det]
  Hint (hidden := true) "`exact isEigenvalue_of_row_sums A.transpose c h`."
  exact isEigenvalue_of_row_sums A.transpose c h

end LinearAlgebraGame

Conclusion "**Yes** — but the eigenvector is no longer $(1,\\dots,1)$: try $A = \\begin{pmatrix}1&1\\\\0&0\\end{pmatrix}$, whose columns sum to $1$."

NewTheorem LinearAlgebraGame.isEigenvalue_of_row_sums Matrix.transpose_sub Matrix.transpose_smul
TheoremTab "Eigen"
