import Game.Levels.MatrixOfMap.L02_RepresentH

World "MatrixOfMap"
Level 3
Title "Rotation about the x-axis"

-- @sheet 5 Q5a
/-! @answer
The rotation fixes $\vec e_1$ and turns the $yz$-plane. Seen from the head at $(1,0,0)$
looking down at the origin, $\vec e_2$ points right and $\vec e_3$ points up, so a
**clockwise** turn by $\theta$ sends $\vec e_2 \mapsto \cos\theta\,\vec e_2 - \sin\theta\,\vec e_3$
and $\vec e_3 \mapsto \sin\theta\,\vec e_2 + \cos\theta\,\vec e_3$. The images are the columns:
$$\begin{pmatrix}1&0&0\\0&\cos\theta&\sin\theta\\0&-\sin\theta&\cos\theta\end{pmatrix}.$$
It is a rotation: $R^{\mathsf T}R = I$ (columns orthonormal, using $\sin^2\theta+\cos^2\theta = 1$)
and $\det R = 1$. (The counter-clockwise convention gives the transpose.)
-/
Introduction "
**Problem Sheet 5, Question 5(a).** Rotation of all vectors in three-space through an angle
$\\theta$ about the $x$-axis is a transformation of $\\mathbb R^3$. Represent it with respect to
the standard bases. Arrange the rotation so that to someone whose feet are at the origin and
whose head is at $(1, 0, 0)$, the movement appears clockwise.

\"Clockwise\" is a picture, so Lean needs it as a formula. Looking down from $(1,0,0)$,
$\\vec e_2$ points right and $\\vec e_3$ points up; clockwise means $\\vec e_2$ starts moving
*down*, towards $-\\vec e_3$. So we ask for a matrix $R$ that is
* a rotation: $R^{\\mathsf T} R = I$ and $\\det R = 1$;
* about the $x$-axis: $R\\vec e_1 = \\vec e_1$;
* clockwise for that observer: $R\\vec e_2 = (0, \\cos\\theta, -\\sin\\theta)$.

These four facts pin $R$ down completely. Find it (`use !![…]`), then check them.
"

namespace LinearAlgebraGame

open Matrix in
/-- There is a rotation matrix $R$ ($R^{\mathsf T}R = I$, $\det R = 1$) fixing $\vec e_1$ and
sending $\vec e_2$ to $(0, \cos\theta, -\sin\theta)$. -/
Statement (θ : ℝ) : ∃ R : Matrix (Fin 3) (Fin 3) ℝ, Rᵀ * R = 1 ∧ R.det = 1 ∧
    R *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧ R *ᵥ ![0, 1, 0] = ![0, Real.cos θ, -Real.sin θ] := by
  Hint "Column $j$ of $R$ is $R\\vec e_j$. You know columns 1 and 2; column 3 must be a unit
  vector perpendicular to both, chosen so that $\\det R = 1$."
  Hint (hidden := true) "`use !![1, 0, 0; 0, Real.cos θ, Real.sin θ; 0, -Real.sin θ, Real.cos θ]`"
  use !![1, 0, 0; 0, Real.cos θ, Real.sin θ; 0, -Real.sin θ, Real.cos θ]
  Hint (hidden := true) "You will need $\\sin^2\\theta + \\cos^2\\theta = 1$: `have hs := Real.sin_sq_add_cos_sq θ`."
  have hs := Real.sin_sq_add_cos_sq θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · Hint (hidden := true) "`ext i j`, `fin_cases i <;> fin_cases j`, then
    `simp [Matrix.mul_apply, Fin.sum_univ_three]` and `linarith` for the diagonal entries."
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> linarith
  · Hint (hidden := true) "`rw [Matrix.det_fin_three]`, then `simp` and `linear_combination hs`."
    rw [Matrix.det_fin_three]
    simp
    linear_combination hs
  · ext i
    fin_cases i <;> simp
  · ext i
    fin_cases i <;> simp

end LinearAlgebraGame

Conclusion "
$$R_x(\\theta) = \\begin{pmatrix}1&0&0\\\\0&\\cos\\theta&\\sin\\theta\\\\0&-\\sin\\theta&\\cos\\theta\\end{pmatrix}.$$
Take this convention to your tutorial: the counter-clockwise reading gives the transpose.
"

TheoremTab "Matrices"
NewTheorem Matrix.det_fin_three
