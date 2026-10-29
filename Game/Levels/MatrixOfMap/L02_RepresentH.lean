import Game.Levels.MatrixOfMap.L01_Columns

World "MatrixOfMap"
Level 2
Title "Represent h with respect to B, D"

-- @sheet 5 Q4
/-! @answer
Apply $h$ to each vector of $B$ and express the result in
$D = \langle \vec d_1, \vec d_2\rangle = \langle (1,0), (0,2)\rangle$:
$h(1,1,1) = (2,2) = 2\vec d_1 + 1\vec d_2$, $h(1,1,0) = (2,1) = 2\vec d_1 + \tfrac12\vec d_2$,
$h(1,0,0) = (1,1) = 1\vec d_1 + \tfrac12\vec d_2$. These coordinate vectors are the columns, so
$$\mathrm{Rep}_{B,D}(h) = \begin{pmatrix} 2 & 2 & 1 \\ 1 & \tfrac12 & \tfrac12 \end{pmatrix}.$$
(It is the only such matrix, because coordinates with respect to the basis $D$ are unique.)
-/
Introduction "
**Problem Sheet 5, Question 4.** Represent the homomorphism $h : \\mathbb R^3 \\to \\mathbb R^2$
$$h(x, y, z) = (x + y,\\ x + z)$$
with respect to
$B = \\langle (1,1,1), (1,1,0), (1,0,0) \\rangle$ and $D = \\langle (1,0), (0,2) \\rangle$.

In Lean you must **find** the matrix: the goal is `∃ H, IsRep B D h H` — supply your
$H$ with `use !![…]` and check that it represents $h$. (Only one matrix works, since
coordinates with respect to $D$ are unique; the Change of Basis world proves this in general
as `isRep_unique`.)
"

namespace LinearAlgebraGame

/-- There is a matrix representing $h(x,y,z) = (x+y, x+z)$ with respect to
$B = \langle (1,1,1),(1,1,0),(1,0,0)\rangle$, $D = \langle (1,0),(0,2)\rangle$. -/
Statement (h : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (hh : ∀ v, h v = ![v 0 + v 1, v 0 + v 2]) :
    ∃ H : Matrix (Fin 2) (Fin 3) ℝ,
      IsRep ![![1, 1, 1], ![1, 1, 0], ![1, 0, 0]] ![![1, 0], ![0, 2]] h H := by
  Hint "Compute $h(\\vec\\beta_1), h(\\vec\\beta_2), h(\\vec\\beta_3)$ and write each in terms of
  $\\vec\\delta_1 = (1,0)$, $\\vec\\delta_2 = (0,2)$. The coefficients are the columns."
  Hint (hidden := true) "`use !![2, 2, 1; 1, 1/2, 1/2]`"
  use !![2, 2, 1; 1, 1/2, 1/2]
  Hint (hidden := true) "As in the last level: `intro j`, `rw [hh]`, then
  `fin_cases j <;> entrywise <;> norm_num`."
  intro j
  rw [hh]
  fin_cases j <;> entrywise <;> norm_num

end LinearAlgebraGame

Conclusion "
$$\\mathrm{Rep}_{B,D}(h) = \\begin{pmatrix} 2 & 2 & 1 \\\\ 1 & \\tfrac12 & \\tfrac12 \\end{pmatrix}.$$
It is the only matrix that works: coordinates with respect to a basis are unique.
"

TheoremTab "Matrices"
