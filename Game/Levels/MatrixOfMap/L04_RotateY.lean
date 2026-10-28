import Game.Levels.MatrixOfMap.L03_RotateX

World "MatrixOfMap"
Level 4
Title "Rotation about the y-axis"

-- @sheet 5 Q5b
/-! @answer
Now $\vec e_2$ is fixed. Looking down from the head at $\vec e_2$ towards the origin,
$\vec e_3$ points right and $\vec e_1$ points up (since $\vec e_3\times\vec e_1 = \vec e_2$).
Clockwise for this observer sends $\vec e_3 \mapsto \cos\theta\,\vec e_3 - \sin\theta\,\vec e_1$
and $\vec e_1 \mapsto \cos\theta\,\vec e_1 + \sin\theta\,\vec e_3$, so
$$\begin{pmatrix}\cos\theta&0&-\sin\theta\\0&1&0\\\sin\theta&0&\cos\theta\end{pmatrix},$$
which satisfies $R^{\mathsf T}R = I$ and $\det R = 1$.
-/
Introduction "
**Problem Sheet 5, Question 5(b).** Repeat the prior item, only rotate about the $y$-axis
instead. (Put the person's head at $\\vec e_2$.)

The same convention as before, with the axes moved round cyclically
($x \\to y \\to z \\to x$): the observer at $\\vec e_2$ sees $\\vec e_3$ pointing right and
$\\vec e_1$ pointing up, and clockwise means $R\\vec e_3 = (-\\sin\\theta, 0, \\cos\\theta)$.
"

namespace LinearAlgebraGame

open Matrix in
/-- There is a rotation matrix fixing $\vec e_2$ and sending $\vec e_3$ to
$(-\sin\theta, 0, \cos\theta)$. -/
Statement (θ : ℝ) : ∃ R : Matrix (Fin 3) (Fin 3) ℝ, Rᵀ * R = 1 ∧ R.det = 1 ∧
    R *ᵥ ![0, 1, 0] = ![0, 1, 0] ∧ R *ᵥ ![0, 0, 1] = ![-Real.sin θ, 0, Real.cos θ] := by
  Hint "You know columns 2 and 3 of $R$. Column 1 is forced by orthogonality and $\\det R = 1$."
  use !![Real.cos θ, 0, -Real.sin θ; 0, 1, 0; Real.sin θ, 0, Real.cos θ]
  have hs := Real.sin_sq_add_cos_sq θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> linarith
  · rw [Matrix.det_fin_three]
    simp
    linear_combination hs
  · ext i
    fin_cases i <;> simp
  · ext i
    fin_cases i <;> simp

end LinearAlgebraGame

Conclusion "
$$R_y(\\theta) = \\begin{pmatrix}\\cos\\theta&0&-\\sin\\theta\\\\0&1&0\\\\\\sin\\theta&0&\\cos\\theta\\end{pmatrix}.$$
Notice the minus sign is now *above* the diagonal: the cyclic order $x\\to y\\to z\\to x$ puts
$\\vec e_3$ before $\\vec e_1$.
"

TheoremTab "Matrices"
