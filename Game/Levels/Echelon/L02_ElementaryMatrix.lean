import Game.Levels.Echelon.L01_Matrices

World "Echelon"
Level 2
Title "Row operations are matrices"

Introduction "
Every row operation is left multiplication by an *elementary matrix*. The combination
$k\\rho_i + \\rho_j$ is `combo i j k` $= I + k E_{ji}$ (the identity with an extra $k$ in
row $j$, column $i$). Check that `combo 0 1 k` really performs $k\\rho_1 + \\rho_2$ on a
$2\\times n$ matrix: row 1 (Lean counts from 0) is unchanged, and row 2 becomes
$k\\rho_1 + \\rho_2$.

`Matrix.of ![r₀, r₁]` is the matrix with rows `r₀`, `r₁`. To prove matrices equal:
`ext i j` (entry $(i, j)$; `entrywise` needs a known number of columns, and here there are $n$).
The entries of a product unfold with `Matrix.mul_apply` (Theorems tab, **Matrices**):
$(MN)_{ij} = \\sum_k M_{ik}N_{kj}$. Write its full name — a bare `mul_apply` is an unrelated
lemma.

Also new (Definitions tab): `scale i c`, the elementary matrix of $c\\rho_i$ (the identity with
$c$ in place of the $i$-th $1$), and `RowEquiv A B`, \"$B$ comes from $A$ by row operations\":
there are matrices $E$, $F$ with $E A = B$ and $F E = I$ ($E$ records the operations, $F$
undoes them). The conclusion of this level explains why.
"

namespace LinearAlgebraGame

open Matrix in
/-- Left-multiplying by `combo 0 1 k` performs $k\rho_1 + \rho_2$. -/
Statement {n : ℕ} (k : ℝ) (A : Matrix (Fin 2) (Fin n) ℝ) :
    (combo 0 1 k : Matrix (Fin 2) (Fin 2) ℝ) * A = Matrix.of ![A 0, k • A 0 + A 1] := by
  Hint "Compare entries; unfold `combo` and the matrix product."
  ext i j
  Hint (hidden := true) "`fin_cases i <;> simp [combo, Matrix.add_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]`"
  fin_cases i <;> simp [combo, Matrix.add_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

end LinearAlgebraGame

Conclusion "
So a sequence of row operations $A \\to E_1A \\to E_2E_1A \\to \\dots$ is multiplication by one
matrix $E = E_r\\cdots E_1$, and since each step can be undone, $E$ has an inverse $F$
($FE = I$). That is how this game states row equivalence: `RowEquiv A B` means
`∃ E F, F * E = 1 ∧ E * A = B`.
"

NewDefinition LinearAlgebraGame.combo LinearAlgebraGame.scale LinearAlgebraGame.RowEquiv
NewTheorem Matrix.add_mul Matrix.single_apply Matrix.mul_apply
