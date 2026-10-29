import Game.Levels.LeanBasics.L10_DotProduct

World "LeanBasics"
Level 11
Title "Matrix times vector"

Introduction "
A matrix is written row by row: `!![1, 2; 3, 4]` is $\\begin{pmatrix}1&2\\\\3&4\\end{pmatrix}$
(rows separated by `;`). `A *ᵥ v` is the matrix–vector product: entry $i$ of $Av$ is
(row $i$ of $A$) $\\cdot$ $v$.

So this level combines the last two: check entry by entry, and each entry is a dot product.
Add `mulVec` to the list of things `norm_num` should unfold.

**Typing:** `*ᵥ` is `*` then `\\_v`.
"

open Matrix in
/-- $\begin{pmatrix}1&2\\3&4\end{pmatrix}\begin{pmatrix}1\\1\end{pmatrix} = \begin{pmatrix}3\\7\end{pmatrix}$. -/
Statement : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 1] = ![3, 7] := by
  Hint "Entry by entry: `entrywise`."
  entrywise
  · Hint "Entry 0 of $Av$ is (row 0 of $A$) $\\cdot$ $v$ $= 1 \\cdot 1 + 2 \\cdot 1$, which should be $3$.
    Unfold with `norm_num [mulVec, dotProduct, Fin.sum_univ_two]`."
    norm_num [mulVec, dotProduct, Fin.sum_univ_two]
  · Hint "Component `1` (the second row): $3 \\cdot 1 + 4 \\cdot 1 = 7$. Same command as before."
    norm_num [mulVec, dotProduct, Fin.sum_univ_two]

/-- `A *ᵥ v`: the matrix–vector product. -/
DefinitionDoc Matrix.mulVec as "*ᵥ"
NewDefinition Matrix.mulVec
