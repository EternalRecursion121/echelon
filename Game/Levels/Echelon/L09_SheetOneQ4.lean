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

For (c): try writing `IsNonsingular !![1, 2, 1; 1, 3, 1]` — Lean refuses, because the
definition only accepts square matrices. Write your answer to (c) in a comment `-- Explain:`.
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
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    simp [mulVec, dotProduct, Fin.sum_univ_two] at h₀ h₁
    Hint (hidden := true) "`rowop h₁ : v 1 = 0 := h₁ - h₀`, then `rowop h₀ : v 0 = 0 := h₀ - 2 * h₁`."
    rowop h₁ : v 1 = 0 := h₁ - h₀
    rowop h₀ : v 0 = 0 := h₀ - 2 * h₁
    ext i
    fin_cases i <;> simp [h₀, h₁]
  · Hint "(b): row 2 is a multiple of row 1. Find a nonzero solution."
    left
    intro h
    Hint (hidden := true) "`have h₀ := h ![2, -1] (by ext i; fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two])`"
    have h₀ := h ![2, -1] (by ext i; fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two])
    have h₁ := congrFun h₀ 0
    simp at h₁

end LinearAlgebraGame

Conclusion "(a) nonsingular, (b) singular, (c) not square — the question does not apply."

NewDefinition LinearAlgebraGame.IsNonsingular
