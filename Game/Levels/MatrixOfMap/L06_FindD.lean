import Game.Levels.MatrixOfMap.L05_FunctionSpace

World "MatrixOfMap"
Level 6
Title "Choose the codomain basis"

-- @sheet 7 Q2
/-! @answer
The projection is $p(x,y,z) = (x, y, 0)$. Column $j$ of $H$ must be $\mathrm{Rep}_D(p(\vec e_j))$:
$p(\vec e_1) = \vec e_1 = 1\delta_1 + 2\delta_2$, $p(\vec e_2) = \vec e_2 = \delta_3$, and
$p(\vec e_3) = \vec 0$ (third column zero, fine). So $\delta_3 = \vec e_2$ and
$\delta_1 + 2\delta_2 = \vec e_1$. Choosing $\delta_2 = \vec e_3$ forces $\delta_1 = (1, 0, -2)$:
$$D = \langle (1,0,-2),\ (0,0,1),\ (0,1,0) \rangle .$$
These three vectors are independent (if $a\delta_1 + b\delta_2 + c\delta_3 = 0$ then the first
component gives $a = 0$, then $c = 0$ and $b = 0$), so $D$ is a basis. Other choices of
$\delta_2$ also work.
-/
Introduction "
**Problem Sheet 7, Question 2.** Find a basis $D$ for $\\mathbb R^3$ such that, with respect to
$\\mathcal E_3, D$, the matrix
$$H = \\begin{pmatrix}1&0&0\\\\2&0&0\\\\0&1&0\\end{pmatrix}$$
represents projection onto the $xy$ plane from $\\mathbb R^3$ to $\\mathbb R^3$.

\"Basis\" here: three linearly independent vectors in $\\mathbb R^3$.
"

namespace LinearAlgebraGame

/-- There are three independent vectors $D$ such that $H$ represents the projection
$p(x,y,z) = (x,y,0)$ with respect to $\mathcal E_3, D$. -/
Statement (p : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (hp : ∀ v, p v = ![v 0, v 1, 0]) :
    ∃ D : Fin 3 → (Fin 3 → ℝ), LinearIndependent ℝ D ∧
      IsRep ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] D p !![1, 0, 0; 2, 0, 0; 0, 1, 0] := by
  Hint "Column $j$ says $p(\\vec e_j) = h_\{1j}\\vec\\delta_1 + h_\{2j}\\vec\\delta_2 + h_\{3j}\\vec\\delta_3$.
  Column 2 tells you $\\vec\\delta_3$ outright. Column 1 gives one equation linking
  $\\vec\\delta_1$ and $\\vec\\delta_2$: you are free to choose one of them."
  use ![![1, 0, -2], ![0, 0, 1], ![0, 1, 0]]
  constructor
  · Hint "Independence: suppose a combination is zero and look at each component."
    Hint (hidden := true) "`rw [Fintype.linearIndependent_iff]`, `intro g hg`, then take
    components `have h0 := congrFun hg 0` (and 1, 2), `simp [Fin.sum_univ_three] at h0 h1 h2`,
    and finish with `intro i; fin_cases i <;> simp <;> linarith`."
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    have h2 := congrFun hg 2
    simp [Fin.sum_univ_three] at h0 h1 h2
    intro i
    fin_cases i <;> simp <;> linarith
  · Hint "Now check the three columns."
    Hint (hidden := true) "`intro j`, `rw [hp]`, then `fin_cases j <;> entrywise <;> norm_num`."
    intro j
    rw [hp]
    fin_cases j <;> entrywise <;> norm_num

end LinearAlgebraGame

Conclusion "
$D = \\langle (1,0,-2), (0,0,1), (0,1,0)\\rangle$ works; any $\\vec\\delta_2$ that keeps $D$ a basis
(with $\\vec\\delta_1 = \\vec e_1 - 2\\vec\\delta_2$) does too.
"

TheoremTab "Matrices"
