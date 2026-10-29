import Game.Levels.Echelon.L06_SheetOneQ11

World "Echelon"
Level 7
Title "An invariant of row equivalence"

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

Decide with `left` (no) or `right` (yes). Row operations change a matrix, but some things
survive them (the previous levels found one: the solutions of the homogeneous system). Do
these two matrices agree on such things?
"

namespace LinearAlgebraGame

open Matrix in
/-- Are these two matrices row equivalent? -/
Statement : (¬ RowEquiv (!![1, 1, 1; 0, 0, 3] : Matrix (Fin 2) (Fin 3) ℝ) !![0, 1, 2; 1, -1, 1]) ∨
    RowEquiv (!![1, 1, 1; 0, 0, 3] : Matrix (Fin 2) (Fin 3) ℝ) !![0, 1, 2; 1, -1, 1] := by
  Hint "Compare the solutions of the two homogeneous systems."
  Hint (hidden := true) "Find a vector killed by the first matrix but not by the second."
  left
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
