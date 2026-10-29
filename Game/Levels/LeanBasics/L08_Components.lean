import Game.Levels.LeanBasics.L07_Or

World "LeanBasics"
Level 8
Title "Vectors: components"

Introduction "
In this game a vector in $\\mathbb R^n$ is written with square brackets after an
exclamation mark: `![3, 7]` is the vector $\\begin{pmatrix}3\\\\7\\end{pmatrix}$ in $\\mathbb R^2$.

A vector is really a *function* from positions to numbers, so `v 0` is its first entry and
`v 1` its second. **Positions are numbered from 0.**

`norm_num` can read off an entry of a vector written out like this.
"

/-- The second entry of $(3, 7)$ is $7$. -/
Statement : (![3, 7] : Fin 2 → ℝ) 1 = 7 := by
  Hint "Position `1` is the *second* entry. The calculator can evaluate it."
  Hint (hidden := true) "`norm_num`"
  norm_num

Conclusion "`Fin 2` is the set of positions $\\{0, 1\\}$, and `Fin 2 → ℝ` is $\\mathbb R^2$."

NewDefinition Fin
