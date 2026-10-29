import Game.Levels.Echelon.L11_FirstColumn

World "Echelon"
Level 12
Title "Row-equivalence classes: a zero first column"

-- @sheet 2 Q8
/-! @answer
Class of $\begin{pmatrix}0&1\\0&0\end{pmatrix}$: **the nonzero matrices with zero first column**,
$\begin{pmatrix}0&p\\0&q\end{pmatrix}$ with $(p,q) \ne (0,0)$. Indeed
$E\begin{pmatrix}0&1\\0&0\end{pmatrix} = \begin{pmatrix}0&e_{11}\\0&e_{21}\end{pmatrix}$ and the
first column of an invertible $E$ is nonzero; conversely if $p \ne 0$ take
$E = \begin{pmatrix}p&0\\q&1\end{pmatrix}$, if $q \ne 0$ take $E = \begin{pmatrix}p&1\\q&0\end{pmatrix}$
(both invertible).
-/
Introduction "
**Problem Sheet 2, Question 8 (part 2).** Describe the matrices in the class of
$\\begin{pmatrix}0&1\\\\0&0\\end{pmatrix}$.

Tools: `firstCol_ne_zero` (last level), `exists_firstCol`, and `rowEquiv_of_det`.
"

namespace LinearAlgebraGame

open Matrix in
/-- The class of $\begin{pmatrix}0&1\\0&0\end{pmatrix}$: the matrices $\begin{pmatrix}0&p\\0&q\end{pmatrix}$
with $(p, q) \ne (0, 0)$. -/
Statement (B : Matrix (Fin 2) (Fin 2) ℝ) :
    RowEquiv !![0, 1; 0, 0] B ↔ ∃ p q, (p ≠ 0 ∨ q ≠ 0) ∧ B = !![0, p; 0, q] := by
  constructor
  · intro h
    obtain ⟨E, F, hFE, hE⟩ := h
    Hint "Compute $E$ times the class representative: it is built from $E$'s first column."
    Hint (hidden := true) "`use E 0 0, E 1 0`, then `constructor`."
    use E 0 0, E 1 0
    constructor
    · Hint (hidden := true) "`exact firstCol_ne_zero E F hFE`"
      exact firstCol_ne_zero E F hFE
    · Hint (hidden := true) "`rw [← hE]`, then `entrywise <;> simp [mul_apply, Fin.sum_univ_two]`."
      rw [← hE]
      entrywise <;> simp [mul_apply, Fin.sum_univ_two]
  · intro h
    obtain ⟨p, q, hpq, hB⟩ := h
    Hint "Build an invertible $E$ whose first column is $(p, q)$."
    Hint (hidden := true) "`obtain ⟨E, hdet, h0, h1⟩ := exists_firstCol hpq`, then
    `apply rowEquiv_of_det E hdet`."
    obtain ⟨E, hdet, h0, h1⟩ := exists_firstCol hpq
    apply rowEquiv_of_det E hdet
    Hint (hidden := true) "`rw [hB]`, then `entrywise <;> simp [mul_apply, Fin.sum_univ_two, h0, h1]`."
    rw [hB]
    entrywise <;> simp [mul_apply, Fin.sum_univ_two, h0, h1]

end LinearAlgebraGame

Conclusion "
Class of $\\begin{pmatrix}0&1\\\\0&0\\end{pmatrix}$: the nonzero matrices with first column zero.
"
