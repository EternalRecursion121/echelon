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
  Hint (hidden := true) "Split into the two columns with `fin_cases j`, then compare the
  vectors entry by entry: `fin_cases j <;> entrywise <;> norm_num`. (`entrywise` writes out the
  sum $\\sum_i$ for you.)"
  fin_cases j <;> entrywise <;> norm_num

end LinearAlgebraGame

Conclusion "
Column 1 is $h(\\vec e_1) = (1, 3)$ and column 2 is $h(\\vec e_2) = (2, 0)$: the columns of
the representation are the (coordinates of the) images of the basis vectors.

This is what makes the matrix *useful* (Hefferon Theorem Three.III.1.9): if $\\vec v$ has
coordinates $\\mathrm{Rep}_B(\\vec v)$ then
$$\\mathrm{Rep}_{B,D}(h)\\cdot\\mathrm{Rep}_B(\\vec v) = \\mathrm{Rep}_D(h(\\vec v)),$$
because $\\vec v = \\sum_j v_j\\vec\\beta_j$ and $h$ is linear. With standard bases on both sides
the coordinates are the vectors themselves, so $h(\\vec v) = H\\vec v$.
"

NewDefinition LinearAlgebraGame.IsRep
TheoremTab "Matrices"
