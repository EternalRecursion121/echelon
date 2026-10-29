import Game.Levels.Echelon.L08_SheetTwoQ2

World "Echelon"
Level 9
Title "Singular or nonsingular?"

-- @sheet 1 Q4
/-! @answer
(a) $\begin{pmatrix}1&2\\1&3\end{pmatrix}$ is **nonsingular**: $x + 2y = 0,\ x + 3y = 0$ gives
$y = 0$ (subtract) and then $x = 0$.
(b) $\begin{pmatrix}1&2\\-3&-6\end{pmatrix}$ is **singular**: row 2 is $-3\times$ row 1, and
$(2, -1)$ is a nonzero solution of the homogeneous system.
(c) $\begin{pmatrix}1&2&1\\1&3&1\end{pmatrix}$ is not square, so **"singular" does not apply**
(the definition is only for square matrices).
-/
Introduction "
**Problem Sheet 1, Question 4.** Singular or nonsingular?
(a) $\\begin{pmatrix}1&2\\\\1&3\\end{pmatrix}$ (b) $\\begin{pmatrix}1&2\\\\-3&-6\\end{pmatrix}$
(c) $\\begin{pmatrix}1&2&1\\\\1&3&1\\end{pmatrix}$

`IsNonsingular A` (Hefferon One.I.2.13): $A$ is square and $A\\vec v = \\vec 0$ only for
$\\vec v = \\vec 0$. Decide (a) and (b) with `left` (singular) or `right` (nonsingular).

The Lean claim covers (a) and (b). For (c), read the definition (One.I.2.13) carefully and
write your answer, with its reason, in a comment `-- Explain:` inside your proof.
"

namespace LinearAlgebraGame

open Matrix in
/-- (a) and (b): singular or nonsingular? -/
Statement : ((¬ IsNonsingular !![(1 : ℝ), 2; 1, 3]) ∨ IsNonsingular !![(1 : ℝ), 2; 1, 3]) ∧
    ((¬ IsNonsingular !![(1 : ℝ), 2; -3, -6]) ∨ IsNonsingular !![(1 : ℝ), 2; -3, -6]) := by
  Hint (hidden := true) "Model answer for (c): the matrix is $2\\times 3$, not square; singular /
  nonsingular is only defined for square matrices."
  constructor
  · Hint "(a): solve the homogeneous system."
    right
    intro v h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    Hint (hidden := true) "`rowop h1 : v 1 = 0 := h1 - h0`, then `rowop h0 : v 0 = 0 := h0 - 2 * h1`."
    rowop h1 : v 1 = 0 := h1 - h0
    rowop h0 : v 0 = 0 := h0 - 2 * h1
    entrywise
    · exact h0
    · exact h1
  · Hint "(b): solve the homogeneous system again. Is $\\vec v = \\vec 0$ forced this time?"
    left
    Hint "Row 2 is a multiple of row 1, so there is a nonzero solution. Assume nonsingularity
    and feed it that solution."
    intro h
    Hint (hidden := true) "`have h0 := h ![2, -1] (by entrywise <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two])`"
    have h0 := h ![2, -1] (by entrywise <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two])
    have h1 := congrFun h0 0
    simp at h1

end LinearAlgebraGame

Conclusion "(a) nonsingular, (b) singular, (c) not square — the question does not apply."

NewDefinition LinearAlgebraGame.IsNonsingular
