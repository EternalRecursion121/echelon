import Game.Levels.Echelon.L07_SheetOneQ12

World "Echelon"
Level 8
Title "Is any row operation redundant?"

-- @sheet 2 Q2
/-! @answer
**Yes: swapping is redundant.** To swap rows $i$ and $j$: $\rho_j \leftarrow \rho_j + \rho_i$,
then $\rho_i \leftarrow \rho_i - \rho_j$ (now $-$old $\rho_j$), then $\rho_j \leftarrow \rho_j + \rho_i$
(now old $\rho_i$), then $\rho_i \leftarrow -1\cdot\rho_i$. As matrices (rows $1, 2$):
$\begin{pmatrix}0&1\\1&0\end{pmatrix} = \begin{pmatrix}-1&0\\0&1\end{pmatrix}
\begin{pmatrix}1&0\\1&1\end{pmatrix}\begin{pmatrix}1&-1\\0&1\end{pmatrix}
\begin{pmatrix}1&0\\1&1\end{pmatrix}$. The other two are not redundant. *Rescaling:* on
$1\times 1$ matrices there is nothing to swap and no second row to add, so only rescaling can
turn $(1)$ into $(2)$. *Combination:* a product of rescaling and swap matrices has exactly one
nonzero entry in each row, so it can never equal $\begin{pmatrix}1&0\\1&1\end{pmatrix}$, whose
second row has two.
-/
Introduction "
**Problem Sheet 2, Question 2.** Are any of the operations used in Gauss's Method redundant?
That is, can we make any of the operations from a combination of the others?

The claim tested: the swap $\\rho_1 \\leftrightarrow \\rho_2$, i.e. the matrix
$\\begin{pmatrix}0&1\\\\1&0\\end{pmatrix}$, is a product of combination and rescaling matrices
(`NoSwapOps`). `Submonoid.closure NoSwapOps` is the set of all such products. Decide with
`left` (no: the swap is not such a product) or `right` (yes), then prove your choice.
`∉` (\"not in\") is typed `\\notin`.
"

namespace LinearAlgebraGame

open Matrix in
/-- Is the swap matrix a product of combination and rescaling matrices? -/
Statement : ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ∉ Submonoid.closure NoSwapOps) ∨
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ∈ Submonoid.closure NoSwapOps := by
  Hint "Decide first: experiment on paper with a $2\\times 2$ matrix — what can you reach using
  only $\\rho_j \\leftarrow \\rho_j + k\\rho_i$ and rescaling?"
  right
  Hint "Write the swap as a product of combination and rescaling matrices (`scale`, `combo`),
  then show each factor is in `NoSwapOps`. A product of members of the closure is a member
  (`Submonoid.mul_mem`), and so is every member of `NoSwapOps` (`Submonoid.subset_closure`)."
  Hint (hidden := true) "Add row 1 to row 2, subtract row 2 from row 1, add row 1 to row 2, negate row 1:
  `rw [show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = scale 0 (-1) * combo 0 1 1 * combo 1 0 (-1) * combo 0 1 1 by …]`
  where `…` is `ext i j` and `fin_cases i <;> fin_cases j <;> simp [scale, combo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Function.update]`."
  rw [show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      scale 0 (-1) * combo 0 1 1 * combo 1 0 (-1) * combo 0 1 1 by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scale, combo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Function.update]]
  Hint (hidden := true) "`apply Submonoid.mul_mem` three times, then each factor:
  `apply Submonoid.subset_closure`, choose `left` (combination) or `right` (rescaling), `use …`."
  apply Submonoid.mul_mem
  apply Submonoid.mul_mem
  apply Submonoid.mul_mem
  · apply Submonoid.subset_closure
    right
    use 0, -1
    norm_num
  · apply Submonoid.subset_closure
    left
    use 0, 1, 1
    simp
  · apply Submonoid.subset_closure
    left
    use 1, 0, -1
    simp
  · apply Submonoid.subset_closure
    left
    use 0, 1, 1
    simp

end LinearAlgebraGame

Conclusion "**Answer: yes** — swapping is built from three combinations and one rescaling by $-1$."

NewDefinition LinearAlgebraGame.NoSwapOps
