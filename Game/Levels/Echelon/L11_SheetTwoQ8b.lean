import Game.Levels.Echelon.L10_SheetTwoQ8a

World "Echelon"
Level 11
Title "Row-equivalence classes: rank one"

-- @sheet 2 Q8
/-! @answer
Class of $\begin{pmatrix}0&1\\0&0\end{pmatrix}$: **the nonzero matrices with zero first column**,
$\begin{pmatrix}0&p\\0&q\end{pmatrix}$ with $(p,q) \ne (0,0)$.
Class of $\begin{pmatrix}1&a\\0&0\end{pmatrix}$: **the matrices $\begin{pmatrix}p&ap\\q&aq\end{pmatrix}$
with $(p,q) \ne (0,0)$** — nonzero first column, second column $= a\,\times$ first.
Indeed $E\begin{pmatrix}1&a\\0&0\end{pmatrix} = \begin{pmatrix}e_{11}&ae_{11}\\e_{21}&ae_{21}\end{pmatrix}$
and the first column of an invertible $E$ is nonzero; conversely if $p \ne 0$ take
$E = \begin{pmatrix}p&0\\q&1\end{pmatrix}$, if $q \ne 0$ take $E = \begin{pmatrix}p&1\\q&0\end{pmatrix}$
(both invertible). Same argument for the other class.
-/
Introduction "
**Problem Sheet 2, Question 8 (part 2).** Describe the matrices in the class of
$\\begin{pmatrix}0&1\\\\0&0\\end{pmatrix}$ and in the class of $\\begin{pmatrix}1&a\\\\0&0\\end{pmatrix}$.

`not_and_or : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q` turns \"not both zero\" into \"one is nonzero\".
"

namespace LinearAlgebraGame

open Matrix in
/-- The two rank-one classes, described. -/
Statement (a : ℝ) :
    (∀ B : Matrix (Fin 2) (Fin 2) ℝ,
      RowEquiv !![0, 1; 0, 0] B ↔ ∃ p q, (p ≠ 0 ∨ q ≠ 0) ∧ B = !![0, p; 0, q]) ∧
    (∀ B : Matrix (Fin 2) (Fin 2) ℝ,
      RowEquiv !![1, a; 0, 0] B ↔ ∃ p q, (p ≠ 0 ∨ q ≠ 0) ∧ B = !![p, a * p; q, a * q]) := by
  constructor
  · intro B
    constructor
    · intro h
      obtain ⟨E, F, hFE, hE⟩ := h
      Hint "Compute $E$ times the class representative: it is built from $E$'s first column."
      use E 0 0, E 1 0
      constructor
      · Hint (hidden := true) "`rw [← not_and_or]`, `intro h0`; then entry $(0,0)$ of $FE = I$ is $0 = 1$:
        `have h1 := congrFun (congrFun hFE 0) 0` and `simp [mul_apply, Fin.sum_univ_two, h0.1, h0.2] at h1`."
        rw [← not_and_or]
        intro h0
        have h1 := congrFun (congrFun hFE 0) 0
        simp [mul_apply, Fin.sum_univ_two, h0.1, h0.2] at h1
      · rw [← hE]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
    · intro h
      obtain ⟨p, q, hpq, hB⟩ := h
      Hint "Build an invertible $E$ whose first column is $(p, q)$ — the choice depends on which is nonzero."
      rcases hpq with hp | hq
      · apply rowEquiv_of_det !![p, 0; q, 1]
        · simp [det_fin_two, hp]
        · rw [hB]
          ext i j
          fin_cases i <;> fin_cases j <;> simp
      · apply rowEquiv_of_det !![p, 1; q, 0]
        · simp [det_fin_two, hq]
        · rw [hB]
          ext i j
          fin_cases i <;> fin_cases j <;> simp
  · intro B
    constructor
    · intro h
      obtain ⟨E, F, hFE, hE⟩ := h
      use E 0 0, E 1 0
      constructor
      · rw [← not_and_or]
        intro h0
        have h1 := congrFun (congrFun hFE 0) 0
        simp [mul_apply, Fin.sum_univ_two, h0.1, h0.2] at h1
      · rw [← hE]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, mul_comm]
    · intro h
      obtain ⟨p, q, hpq, hB⟩ := h
      rcases hpq with hp | hq
      · apply rowEquiv_of_det !![p, 0; q, 1]
        · simp [det_fin_two, hp]
        · rw [hB]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
      · apply rowEquiv_of_det !![p, 1; q, 0]
        · simp [det_fin_two, hq]
        · rw [hB]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]

end LinearAlgebraGame

Conclusion "
Class of $\\begin{pmatrix}0&1\\\\0&0\\end{pmatrix}$: nonzero, first column zero. Class of
$\\begin{pmatrix}1&a\\\\0&0\\end{pmatrix}$: nonzero first column, second column $a$ times the first.
"
NewTheorem not_and_or mul_comm
