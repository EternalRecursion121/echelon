import Game.Metadata
import Game.Ch1

World "Echelon"
Level 1
Title "A system is a matrix equation"

Introduction "
Hefferon One.III: from now on a system is $A\\vec x = \\vec b$. Sheet 1 Q1's system
$x - z = 0,\\ 3x + y = 1,\\ -x + y + z = 4$ has coefficient matrix
$\\begin{pmatrix}1&0&-1\\\\3&1&0\\\\-1&1&1\\end{pmatrix}$. Check its solution in matrix form.

New: `simp` — a general simplifier; `simp [mulVec, dotProduct, Fin.sum_univ_three]` writes a
row times a vector out. `t₁ <;> t₂` runs `t₂` on every goal `t₁` produces.
"

namespace LinearAlgebraGame

open Matrix in
/-- $\begin{pmatrix}1&0&-1\\3&1&0\\-1&1&1\end{pmatrix}\begin{pmatrix}-1\\4\\-1\end{pmatrix}
= \begin{pmatrix}0\\1\\4\end{pmatrix}$. -/
Statement : (!![1, 0, -1; 3, 1, 0; -1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![-1, 4, -1] = ![0, 1, 4] := by
  Hint "Compare components: `ext i`, then `fin_cases i`."
  ext i
  Hint (hidden := true) "`fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num`"
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num

end LinearAlgebraGame

Conclusion "Matrix form and equation form are the same system."

TheoremTab "Matrices"
NewTactic simp
