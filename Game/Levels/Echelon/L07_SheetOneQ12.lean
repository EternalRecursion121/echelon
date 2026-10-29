import Game.Levels.Echelon.L06_SheetOneQ11

World "Echelon"
Level 7
Title "Row equivalent?"

-- @sheet 1 Q12
/-! @answer
**No.** If $B = EA$ for a matrix $E$ (a product of elementary matrices) then every solution of
$A\vec x = \vec 0$ is a solution of $B\vec x = \vec 0$, since $B\vec x = E(A\vec x)$. Here
$\vec x = (1, -1, 0)$ solves $A\vec x = \vec 0$ for $A = \begin{pmatrix}1&1&1\\0&0&3\end{pmatrix}$,
but $B\vec x = (-1, 2) \ne \vec 0$ for $B = \begin{pmatrix}0&1&2\\1&-1&1\end{pmatrix}$. (Equally:
their reduced echelon forms $\begin{pmatrix}1&1&0\\0&0&1\end{pmatrix}$ and
$\begin{pmatrix}1&0&3\\0&1&2\end{pmatrix}$ differ.)
-/
Introduction "
**Problem Sheet 1, Question 12.** Are the matrices
$\\begin{pmatrix}1&1&1\\\\0&0&3\\end{pmatrix}$ and $\\begin{pmatrix}0&1&2\\\\1&-1&1\\end{pmatrix}$
row equivalent?

Decide with `left` (no) or `right` (yes), then prove your choice: \"yes\" by exhibiting the
row operations (an invertible $E$ with $EA = B$), \"no\" by finding something that row
operations do not change on which the two matrices differ.
"

namespace LinearAlgebraGame

open Matrix in
/-- Are these two matrices row equivalent? -/
Statement : (¬ RowEquiv (!![1, 1, 1; 0, 0, 3] : Matrix (Fin 2) (Fin 3) ℝ) !![0, 1, 2; 1, -1, 1]) ∨
    RowEquiv (!![1, 1, 1; 0, 0, 3] : Matrix (Fin 2) (Fin 3) ℝ) !![0, 1, 2; 1, -1, 1] := by
  Hint "Decide first: bring both matrices to reduced echelon form on paper."
  left
  Hint "Row operations do not change the solutions of the homogeneous system (the previous
  levels). Compare those solutions for the two matrices."
  Hint (hidden := true) "Find a vector killed by the first matrix but not by the second."
  intro h
  obtain ⟨E, F, hFE, hE⟩ := h
  Hint (hidden := true) "$(1, -1, 0)$: `have h1 : (!![1, 1, 1; 0, 0, 3] : Matrix (Fin 2) (Fin 3) ℝ) *ᵥ ![1, -1, 0] = 0`."
  have h1 : (!![1, 1, 1; 0, 0, 3] : Matrix (Fin 2) (Fin 3) ℝ) *ᵥ ![1, -1, 0] = 0 := by
    entrywise <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
  Hint (hidden := true) "Transport it: `rw [← hE, ← mulVec_mulVec, h1, mulVec_zero]`."
  have h2 : (!![0, 1, 2; 1, -1, 1] : Matrix (Fin 2) (Fin 3) ℝ) *ᵥ ![1, -1, 0] = 0 := by
    rw [← hE, ← mulVec_mulVec, h1, mulVec_zero]
  have h3 := congrFun h2 0
  simp [mulVec, dotProduct, Fin.sum_univ_three] at h3

end LinearAlgebraGame

Conclusion "**Answer: no.** $(1,-1,0)$ is in the null space of the first matrix but not the second."

NewTheorem Submonoid.mul_mem Submonoid.subset_closure
