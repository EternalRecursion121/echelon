import Game.Metadata
import Game.Ch3b

World "MatrixOfMap"
Level 1
Title "Columns are images"

Introduction "
Hefferon's Definition Three.III.1.2: to represent $h : V \\to W$ with respect to bases
$B = \\langle \\vec\\beta_1, \\dots, \\vec\\beta_n\\rangle$ and $D = \\langle \\vec\\delta_1, \\dots, \\vec\\delta_m\\rangle$,
write each image $h(\\vec\\beta_j)$ in terms of $D$:
$$h(\\vec\\beta_j) = h_{1j}\\vec\\delta_1 + \\dots + h_{mj}\\vec\\delta_m .$$
The coefficients form **column $j$** of $\\mathrm{Rep}_{B,D}(h)$.

In this game that is `IsRep B D h H`, which unfolds to
`∀ j, h (B j) = ∑ i, H i j • D i`.

Here $h(x, y) = (x + 2y,\\ 3x)$ and both bases are standard. Check that the matrix
below represents $h$.
"

namespace LinearAlgebraGame

/-- With respect to the standard bases, $h(x,y) = (x+2y, 3x)$ is represented by
$\begin{pmatrix}1&2\\3&0\end{pmatrix}$. -/
Statement (h : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (hh : ∀ v, h v = ![v 0 + 2 * v 1, 3 * v 0]) :
    IsRep ![![1, 0], ![0, 1]] ![![1, 0], ![0, 1]] h !![1, 2; 3, 0] := by
  Hint "There is one equation per column $j$. Introduce `j` and use the formula `{hh}`."
  intro j
  rw [hh]
  Hint (hidden := true) "Split into the two columns with `fin_cases j`, then compare vectors
  componentwise: `ext i` and `fin_cases i`. `simp [Fin.sum_univ_two]` does the arithmetic."
  fin_cases j <;> ext i <;> fin_cases i <;> simp [Fin.sum_univ_two]

end LinearAlgebraGame

Conclusion "
Column 1 is $h(\\vec e_1) = (1, 3)$ and column 2 is $h(\\vec e_2) = (2, 0)$: the columns of
the representation are the (coordinates of the) images of the basis vectors.
"

NewDefinition LinearAlgebraGame.IsRep
TheoremTab "Matrices"
