import Game.Levels.LeanBasics.L10_DotProduct

World "LeanBasics"
Level 11
Title "Matrix times vector"

Introduction "
A matrix is written row by row: `!![1, 2; 3, 4]` is $\\begin{pmatrix}1&2\\\\3&4\\end{pmatrix}$
(rows separated by `;`). In the statement, `(… : Matrix (Fin 2) (Fin 2) ℝ)` tells Lean the
type: a real matrix with rows and columns numbered by `Fin 2` (writing `(x : T)` always means
\"`x`, which has type `T`\"; `(![1, 2] : Fin 2 → ℝ)` was the same for vectors). `A *ᵥ v` is the matrix–vector product: entry $i$ of $Av$ is
(row $i$ of $A$) $\\cdot$ $v$.

So this level combines the last two: check entry by entry, and each entry is a dot product.
With numbers everywhere `norm_num` does each entry. (With letters you would unfold by hand:
`norm_num [mulVec, dotProduct, Fin.sum_univ_two]` — `mulVec` is the name of `*ᵥ`.)

**Typing:** `*ᵥ` is `*` then `\\_v`.
"

open Matrix in
/-- $\begin{pmatrix}1&2\\3&4\end{pmatrix}\begin{pmatrix}1\\1\end{pmatrix} = \begin{pmatrix}3\\7\end{pmatrix}$. -/
Statement : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 1] = ![3, 7] := by
  Hint "Entry by entry: `entrywise`."
  entrywise
  · Hint "Entry 0 of $Av$ is (row 0 of $A$) $\\cdot$ $v$ $= 1 \\cdot 1 + 2 \\cdot 1$, which should be $3$."
    Hint (hidden := true) "`norm_num`"
    norm_num
  · Hint "Entry 1 (the second row): $3 \\cdot 1 + 4 \\cdot 1 = 7$. Same command as before."
    norm_num

/-- `A *ᵥ v`: the matrix–vector product. -/
DefinitionDoc Matrix.mulVec as "*ᵥ"
NewDefinition Matrix.mulVec
