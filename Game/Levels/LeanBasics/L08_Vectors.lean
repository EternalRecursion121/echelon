import Game.Levels.LeanBasics.L07_Or

World "LeanBasics"
Level 8
Title "Vectors and matrices"

Introduction "
In this game a vector in $\\mathbb R^n$ is written `![a, b, …]` and a matrix
`!![a, b; c, d]` (rows separated by `;`). `A *ᵥ v` is the matrix–vector product.

Two vectors are equal when they agree in every component. `ext i` asks you to prove that,
and `fin_cases i` splits into one goal per component (numbered from `0`).
"

open Matrix in
/-- $\begin{pmatrix}1&2\\3&4\end{pmatrix}\begin{pmatrix}1\\1\end{pmatrix} = \begin{pmatrix}3\\7\end{pmatrix}$. -/
Statement : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 1] = ![3, 7] := by
  Hint "Compare component by component: `ext i`, then `fin_cases i`."
  ext i
  fin_cases i
  · Hint "Row 1 times the vector. `norm_num [mulVec, dotProduct, Fin.sum_univ_two]` unfolds
    the product and adds it up."
    norm_num [mulVec, dotProduct, Fin.sum_univ_two]
  · norm_num [mulVec, dotProduct, Fin.sum_univ_two]

/-- `A *ᵥ v`: the matrix–vector product. -/
DefinitionDoc Matrix.mulVec as "*ᵥ"
/-- `u ⬝ᵥ v`: the dot product. -/
DefinitionDoc dotProduct as "⬝ᵥ"
/-- $\sum_{i<2} f(i) = f(0) + f(1)$. -/
TheoremDoc Fin.sum_univ_two as "Fin.sum_univ_two" in "Vectors"
NewTactic ext fin_cases
NewTheorem Fin.sum_univ_two
NewDefinition dotProduct Matrix.mulVec
