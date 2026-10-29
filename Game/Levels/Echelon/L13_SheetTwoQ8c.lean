import Game.Levels.Echelon.L12_SheetTwoQ8b

World "Echelon"
Level 13
Title "Row-equivalence classes: rank one"

-- @sheet 2 Q8
/-! @answer
Class of $\begin{pmatrix}1&a\\0&0\end{pmatrix}$: **the matrices $\begin{pmatrix}p&ap\\q&aq\end{pmatrix}$
with $(p,q) \ne (0,0)$** — nonzero first column, second column $= a\,\times$ first.
Indeed $E\begin{pmatrix}1&a\\0&0\end{pmatrix} = \begin{pmatrix}e_{11}&ae_{11}\\e_{21}&ae_{21}\end{pmatrix}$
and the first column of an invertible $E$ is nonzero; conversely any nonzero $(p, q)$ is the
first column of an invertible $E$ ($\begin{pmatrix}p&0\\q&1\end{pmatrix}$ or
$\begin{pmatrix}p&1\\q&0\end{pmatrix}$).
-/
Introduction "
**Problem Sheet 2, Question 8 (part 3).** Describe the matrices in the class of
$\\begin{pmatrix}1&a\\\\0&0\\end{pmatrix}$.

The same tools as the last level work; `mul_comm` may be needed to match $E_{00}a$ with $aE_{00}$.
"

namespace LinearAlgebraGame

open Matrix in
/-- The class of $\begin{pmatrix}1&a\\0&0\end{pmatrix}$: the matrices
$\begin{pmatrix}p&ap\\q&aq\end{pmatrix}$ with $(p, q) \ne (0, 0)$. -/
Statement (a : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    RowEquiv !![1, a; 0, 0] B ↔ ∃ p q, (p ≠ 0 ∨ q ≠ 0) ∧ B = !![p, a * p; q, a * q] := by
  constructor
  · intro h
    obtain ⟨E, F, hFE, hE⟩ := h
    Hint "As in the last level, the answer is built from $E$'s first column."
    use E 0 0, E 1 0
    constructor
    · exact firstCol_ne_zero E F hFE
    · Hint (hidden := true) "`rw [← hE]`, then `entrywise <;> simp [mul_apply, Fin.sum_univ_two, mul_comm]`."
      rw [← hE]
      entrywise <;> simp [mul_apply, Fin.sum_univ_two, mul_comm]
  · intro h
    obtain ⟨p, q, hpq, hB⟩ := h
    Hint (hidden := true) "`obtain ⟨E, hdet, h0, h1⟩ := exists_firstCol hpq`, then
    `apply rowEquiv_of_det E hdet`."
    obtain ⟨E, hdet, h0, h1⟩ := exists_firstCol hpq
    apply rowEquiv_of_det E hdet
    rw [hB]
    entrywise <;> simp [mul_apply, Fin.sum_univ_two, h0, h1, mul_comm]

end LinearAlgebraGame

Conclusion "
Class of $\\begin{pmatrix}1&a\\\\0&0\\end{pmatrix}$: nonzero first column, second column $a$ times
the first. Together with level 10 that describes all four classes of Sheet 2 Q8.
"
NewTheorem mul_comm
