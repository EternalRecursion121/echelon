import Game.Levels.Echelon.L10_SheetTwoQ8a

World "Echelon"
Level 11
Title "An invertible matrix has a nonzero first column"

Introduction "
A tool for the last two classes of Sheet 2 Q8. If $FE = I$, then the first column of $E$
cannot be zero: otherwise the first column of $FE$ would be zero too, but the first column
of $I$ is $(1, 0)$.

`not_and_or : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q` turns \"not both zero\" into \"one is nonzero\". For a
matrix equation `h : F * E = 1`, its entry $(0, 0)$ is `congrFun (congrFun h 0) 0`
(`congrFun` twice: once for the row, once for the column).

After this level `firstCol_ne_zero` is in your inventory, together with its converse, granted:
`exists_firstCol` — every nonzero $(p, q)$ is the first column of some $E$ with $\\det E \\ne 0$.
"

namespace LinearAlgebraGame

open Matrix in
/-- If $FE = I$ then the first column of $E$ is not zero. -/
Statement firstCol_ne_zero (E F : Matrix (Fin 2) (Fin 2) ℝ) (h : F * E = 1) :
    E 0 0 ≠ 0 ∨ E 1 0 ≠ 0 := by
  Hint "Turn the goal into \"not both zero\" and assume both are zero."
  Hint (hidden := true) "`rw [← not_and_or]`, then `intro h0`."
  rw [← not_and_or]
  intro h0
  Hint "Look at entry $(0, 0)$ of $FE = I$."
  Hint (hidden := true) "`have h1 := congrFun (congrFun h 0) 0`, then
  `simp [Matrix.mul_apply, Fin.sum_univ_two, h0.1, h0.2] at h1` (`h0.1`, `h0.2` are the two halves of `h0`)."
  have h1 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, h0.1, h0.2] at h1

end LinearAlgebraGame

Conclusion "`firstCol_ne_zero` and `exists_firstCol` are now in your inventory."

NewTheorem not_and_or LinearAlgebraGame.exists_firstCol
