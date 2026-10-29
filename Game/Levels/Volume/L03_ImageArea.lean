import Game.Levels.Volume.L02_DetInv

World "Volume"
Level 3
Title "The area of an image"

-- @sheet 9 Q2
/-! @answer
The rectangle $[1,3]\times[2,5]$ has area $2\cdot 3 = 6$. The matrix has determinant
$2\cdot(-1) - 3\cdot 4 = -14$, and a linear map multiplies every area by $|\det|$
(Theorem Four.II.1.5), so the image (a parallelogram) has area $14 \cdot 6 = 84$.
-/
Introduction "
**Problem Sheet 9, Question 2.** What is the area of the image of the rectangle
$[1..3]\\times[2..5]$ under the action of the matrix $\\begin{pmatrix} 2 & 3 \\\\ 4 & -1\\end{pmatrix}$?

Area here is Lebesgue measure (`volume`, made real by `.toReal`); `Matrix.toLin' T` is the
map $\\vec v \\mapsto T\\vec v$ and `f '' s` is the image of the set `s`. Two facts from
measure theory are granted:

* `volume_image_matrix`: the image of a region under $T$ has $|\\det T|$ times its area
  (Hefferon's Theorem Four.II.1.5);
* `Real.volume_Icc_pi_toReal`: a box $[a_1,b_1]\\times\\cdots$ has volume $\\prod (b_i - a_i)$.

The rectangle is `Set.Icc ![1, 2] ![3, 5]`: the points between the corners $(1,2)$ and $(3,5)$.
"

namespace LinearAlgebraGame

open MeasureTheory in
/-- The image of $[1,3]\times[2,5]$ under $\begin{pmatrix} 2 & 3 \\ 4 & -1\end{pmatrix}$ has area $84$. -/
Statement : (volume (Matrix.toLin' (!![2, 3; 4, -1] : Matrix (Fin 2) (Fin 2) ℝ) ''
    Set.Icc ![1, 2] ![3, 5])).toReal = 84 := by
  Hint "Idea: area of image $= |\\det T| \\cdot$ area of the rectangle."
  Hint (hidden := true) "$|\\det T| = 14$ and the rectangle has area $2 \\cdot 3 = 6$."
  Hint (hidden := true) "`rw [volume_image_matrix, Real.volume_Icc_pi_toReal]`. This leaves a
  side goal: the corners are in the right order."
  rw [volume_image_matrix, Real.volume_Icc_pi_toReal]
  · Hint (hidden := true) "`rw [Matrix.det_fin_two_of, Fin.prod_univ_two]` then `norm_num`."
    rw [Matrix.det_fin_two_of, Fin.prod_univ_two]
    norm_num
  · Hint (hidden := true) "`intro i` then `fin_cases i <;> norm_num`."
    intro i
    fin_cases i <;> norm_num

end LinearAlgebraGame

Conclusion "**Answer: 84.** The orientation is reversed ($\\det < 0$), but area is $|\\det|$ times area."

NewTheorem LinearAlgebraGame.volume_image_matrix Real.volume_Icc_pi_toReal Fin.prod_univ_two
TheoremTab "Det"
NewDefinition Matrix.toLin'
