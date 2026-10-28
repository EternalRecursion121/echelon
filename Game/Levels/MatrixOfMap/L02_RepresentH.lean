import Game.Levels.MatrixOfMap.L01_Columns

World "MatrixOfMap"
Level 2
Title "Represent h with respect to B, D"

-- @sheet 5 Q4
/-! @answer
Apply $h$ to each vector of $B$ and express the result in $D = \langle (1,0), (0,2)\rangle$:
$h(1,1,1) = (2,2) = 2\delta_1 + 1\delta_2$, $h(1,1,0) = (2,1) = 2\delta_1 + \tfrac12\delta_2$,
$h(1,0,0) = (1,1) = 1\delta_1 + \tfrac12\delta_2$. These coordinate vectors are the columns, so
$$\mathrm{Rep}_{B,D}(h) = \begin{pmatrix} 2 & 2 & 1 \\ 1 & \tfrac12 & \tfrac12 \end{pmatrix}.$$
It is the only such matrix, because coordinates with respect to the basis $D$ are unique.
-/
Introduction "
**Problem Sheet 5, Question 4.** Represent the homomorphism $h : \\mathbb R^3 \\to \\mathbb R^2$
$$h(x, y, z) = (x + y,\\ x + z)$$
with respect to
$B = \\langle (1,1,1), (1,1,0), (1,0,0) \\rangle$ and $D = \\langle (1,0), (0,2) \\rangle$.

In Lean you must **find** the matrix: the goal is `∃! H, IsRep B D h H` — supply your
$H$ with `refine ⟨H, ?_, ?_⟩`, check that it represents $h$, and then show no other matrix does.
"

namespace LinearAlgebraGame

/-- There is exactly one matrix representing $h(x,y,z) = (x+y, x+z)$ with respect to
$B = \langle (1,1,1),(1,1,0),(1,0,0)\rangle$, $D = \langle (1,0),(0,2)\rangle$. -/
Statement (h : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (hh : ∀ v, h v = ![v 0 + v 1, v 0 + v 2]) :
    ∃! H, IsRep ![![1, 1, 1], ![1, 1, 0], ![1, 0, 0]] ![![1, 0], ![0, 2]] h H := by
  Hint "Compute $h(\\vec\\beta_1), h(\\vec\\beta_2), h(\\vec\\beta_3)$ and write each in terms of
  $\\vec\\delta_1 = (1,0)$, $\\vec\\delta_2 = (0,2)$. The coefficients are the columns."
  Hint (hidden := true) "`refine ⟨your matrix, ?_, ?_⟩` splits existence and uniqueness."
  refine ⟨!![2, 2, 1; 1, 1/2, 1/2], ?_, ?_⟩
  · Hint (hidden := true) "As in the last level: `intro j`, `rw [hh]`, then
    `fin_cases j <;> ext i <;> fin_cases i <;> simp [Fin.sum_univ_two]`, and `norm_num`
    for any leftover fractions."
    intro j
    rw [hh]
    fin_cases j <;> ext i <;> fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num
  · Hint "Uniqueness: if `H'` also represents $h$, compare the two components of the
    equation for each column $j$."
    intro H hH
    ext i j
    Hint (hidden := true) "`have h0 := congrFun (hH j) 0` and `have h1 := congrFun (hH j) 1`
    give the two component equations; `rw [hh] at h0 h1`, then split with `fin_cases`,
    `simp [Fin.sum_univ_two] at h0 h1 ⊢` and finish with `linarith`."
    have h0 := congrFun (hH j) 0
    have h1 := congrFun (hH j) 1
    rw [hh] at h0 h1
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two] at h0 h1 ⊢ <;> linarith

end LinearAlgebraGame

Conclusion "
$$\\mathrm{Rep}_{B,D}(h) = \\begin{pmatrix} 2 & 2 & 1 \\\\ 1 & \\tfrac12 & \\tfrac12 \\end{pmatrix}.$$
The uniqueness half is why the representation is well defined: coordinates with respect to
a basis are unique.
"

TheoremTab "Matrices"
