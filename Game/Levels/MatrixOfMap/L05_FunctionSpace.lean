import Game.Levels.MatrixOfMap.L04_RotateY

World "MatrixOfMap"
Level 5
Title "A map on a function space"

-- @sheet 7 Q1
/-! @answer
The columns say $h(\beta_1) = 0\cdot\delta_1 + 1\cdot\delta_2 = \cos\theta$ and
$h(\beta_2) = 0$. To apply $h$ to $a\cos\theta + b\sin\theta$, write it in terms of $B$:
$a\cos\theta + b\sin\theta = a(\cos\theta - \sin\theta) + (a + b)\sin\theta$. By linearity
$$h(a\cos\theta + b\sin\theta) = a\cos\theta + (a+b)\cdot 0 = a\cos\theta .$$
So $h$ is the projection onto the $\cos$ direction along $\sin$: $a\cos\theta+b\sin\theta \mapsto a\cos\theta$.
In coordinates $(a,b)$ (with respect to $\langle\cos\theta,\sin\theta\rangle$) it is the matrix
$\begin{pmatrix}1&0\\0&0\end{pmatrix}$.
-/
Introduction "
**Problem Sheet 7, Question 1.** What transformation of
$F = \\{ a\\cos\\theta + b\\sin\\theta \\mid a, b \\in \\mathbb R \\}$ (a vector space of functions
in $\\theta$) is represented with respect to $B = \\langle \\cos\\theta - \\sin\\theta, \\sin\\theta\\rangle$
and $D = \\langle \\cos\\theta + \\sin\\theta, \\cos\\theta\\rangle$ by the matrix
$\\begin{pmatrix}0&0\\\\1&0\\end{pmatrix}$?

**Coordinates.** Write the function $a\\cos\\theta + b\\sin\\theta$ as the pair $(a, b)$. Then
$\\cos\\theta - \\sin\\theta$ is $(1,-1)$, $\\sin\\theta$ is $(0,1)$, $\\cos\\theta+\\sin\\theta$ is
$(1,1)$ and $\\cos\\theta$ is $(1,0)$. (That $\\cos$ and $\\sin$ are independent functions,
so these coordinates are well defined, is the narrative here, not the exercise.)

Your answer is a matrix $C$ describing $h$ in the coordinates $(a, b)$: show that **every**
linear $h$ represented by the given matrix is $v \\mapsto C v$.
"

namespace LinearAlgebraGame

open Matrix in
/-- In coordinates $(a,b) \leftrightarrow a\cos\theta + b\sin\theta$: there is a matrix $C$
such that every map represented by $\begin{pmatrix}0&0\\1&0\end{pmatrix}$ with respect to
$B$, $D$ is multiplication by $C$. -/
Statement : ∃ C : Matrix (Fin 2) (Fin 2) ℝ, ∀ h : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ),
    IsRep ![![1, -1], ![0, 1]] ![![1, 1], ![1, 0]] h !![0, 0; 1, 0] →
    ∀ v, h v = C *ᵥ v := by
  Hint "Read off $h(\\vec\\beta_1)$ and $h(\\vec\\beta_2)$ from the columns. Then write a general
  $(a,b)$ as a combination of $\\vec\\beta_1 = (1,-1)$ and $\\vec\\beta_2 = (0,1)$ and use linearity.
  What does $h$ do to $(a, b)$?"
  Hint (hidden := true) "`use !![1, 0; 0, 0]`"
  use !![1, 0; 0, 0]
  intro h hh v
  Hint "Write $v = v_0\\,\\vec\\beta_1 + (v_0 + v_1)\\,\\vec\\beta_2$."
  Hint (hidden := true) "`have hv : v = v 0 • ![1, -1] + (v 0 + v 1) • ![0, 1] := by
    ext i; fin_cases i <;> simp`"
  have hv : v = v 0 • ![1, -1] + (v 0 + v 1) • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  Hint (hidden := true) "Get the two columns as facts: `have h0 := {hh} 0`, `have h1 := {hh} 1`,
  and tidy them with `simp [Fin.sum_univ_two] at h0 h1`."
  have h0 := hh 0
  have h1 := hh 1
  simp [Fin.sum_univ_two] at h0 h1
  Hint (hidden := true) "`rw [hv, map_add, map_smul, map_smul, h0, h1]`, then compare components."
  rw [hv, map_add, map_smul, map_smul, h0, h1]
  ext i
  fin_cases i <;> simp

end LinearAlgebraGame

Conclusion "
$h(a\\cos\\theta + b\\sin\\theta) = a\\cos\\theta$: $h$ projects onto $\\cos\\theta$ along $\\sin\\theta$.
"

TheoremTab "Matrices"
