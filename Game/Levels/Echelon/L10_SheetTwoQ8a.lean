import Game.Levels.Echelon.L09_SheetOneQ4

World "Echelon"
Level 10
Title "Row-equivalence classes: zero and identity"

-- @sheet 2 Q8
/-! @answer
Class of $Z = \begin{pmatrix}0&0\\0&0\end{pmatrix}$: **only $Z$ itself** ($EZ = Z$).
Class of $I$: **all nonsingular $2\times 2$ matrices**, i.e. $ad - bc \ne 0$: if $B = EI = E$
with $FE = I$ then $\det F\det E = 1$, so $\det B \ne 0$; conversely a nonsingular $B$
equals $B\cdot I$ with $B$ invertible.
-/
Introduction "
**Problem Sheet 2, Question 8 (part 1).** Any $2\\times 2$ matrix lies in one of the classes
of $\\begin{pmatrix}0&0\\\\0&0\\end{pmatrix}$, $\\begin{pmatrix}0&1\\\\0&0\\end{pmatrix}$,
$\\begin{pmatrix}1&0\\\\0&1\\end{pmatrix}$, or $\\begin{pmatrix}1&a\\\\0&0\\end{pmatrix}$ ($a \\in \\mathbb R$).
Describe the matrices in each class.

This level: the classes of the zero matrix and of the identity. Levels 12 and 13 do the
other two. For the identity we use the $2\\times 2$ nonsingularity test $ad - bc \\ne 0$;
`rowEquiv_of_det` and `det_mul`, `det_fin_two` (Chapter Four material, borrowed) help.
"

namespace LinearAlgebraGame

open Matrix in
/-- The class of $Z$ is $\{Z\}$; the class of $I$ is the matrices with $ad - bc \ne 0$. -/
Statement : (∀ B : Matrix (Fin 2) (Fin 2) ℝ, RowEquiv 0 B ↔ B = 0) ∧
    (∀ B : Matrix (Fin 2) (Fin 2) ℝ, RowEquiv 1 B ↔ B 0 0 * B 1 1 - B 0 1 * B 1 0 ≠ 0) := by
  constructor
  · intro B
    constructor
    · Hint "What is $E \\cdot 0$?"
      intro h
      obtain ⟨E, F, hFE, hE⟩ := h
      rw [← hE, Matrix.mul_zero]
    · intro h
      Hint (hidden := true) "No row operations needed: `use 1, 1`, then `simp [h]`."
      use 1, 1
      simp [h]
  · intro B
    constructor
    · intro h
      obtain ⟨E, F, hFE, hE⟩ := h
      Hint "Here $B = E$, and $FE = I$ forces $\\det E \\ne 0$."
      Hint (hidden := true) "`rw [Matrix.mul_one] at hE`, `rw [← hE, ← det_fin_two]`, `intro h0`,
      `have hd := congrArg det hFE`, `rw [det_mul, h0, det_one] at hd`, `simp at hd`."
      rw [Matrix.mul_one] at hE
      rw [← hE, ← det_fin_two]
      intro h0
      have hd := congrArg det hFE
      rw [det_mul, h0, det_one] at hd
      simp at hd
    · intro h
      Hint (hidden := true) "`apply rowEquiv_of_det B`, then `rw [det_fin_two]` and `rw [Matrix.mul_one]`."
      apply rowEquiv_of_det B
      · rw [det_fin_two]
        exact h
      · rw [Matrix.mul_one]

end LinearAlgebraGame

Conclusion "Class of $Z$: just $Z$. Class of $I$: the nonsingular matrices."

NewDefinition Matrix.det
NewTheorem Matrix.det_fin_two LinearAlgebraGame.rowEquiv_of_det Matrix.det_mul Matrix.det_one Matrix.mul_one Matrix.mul_zero congrArg
