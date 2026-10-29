import Game.Levels.Volume.L06_ThreeByThreeArea

World "Volume"
Level 7
Title "The line through two points"

-- @sheet 10 Q1d
/-! @answer
A point $P = (x,y)$ lies on the line through $B$ and $C$ exactly when the triangle $PBC$ is
degenerate, i.e. has area zero. By (c) the equation of the line is
$$\begin{vmatrix} 1&1&1\\ x&x_2&x_3\\ y&y_2&y_3\end{vmatrix} = 0,$$
which expands to $(x_3-x_2)(y-y_2) = (y_3-y_2)(x-x_2)$: a genuine linear equation because
$B \ne C$.
-/
Introduction "
**Problem Sheet 10, Question 1(d).** Use this to write the equation for a line through $B$
and $C$ in terms of a determinant.

Part (c) suggests the answer: $P = (x, y)$ is on the line $BC$ exactly when the triangle
$PBC$ is flat, i.e. has area $0$. Lean checks this: if $B \\ne C$, then $(x, y)$ is on the
line through $B$ and $C$ (that is, $(x,y) = B + t(C - B)$ for some $t$) if and only if the
determinant from (c) with $A = P$ vanishes.
"

namespace LinearAlgebraGame

/-- For $B \ne C$: $(x,y)$ lies on line $BC$ iff $\begin{vmatrix} 1&1&1\\ x&x_2&x_3\\ y&y_2&y_3\end{vmatrix} = 0$. -/
Statement (x y x₂ y₂ x₃ y₃ : ℝ) (hBC : x₂ ≠ x₃ ∨ y₂ ≠ y₃) :
    (∃ t : ℝ, x = x₂ + t * (x₃ - x₂) ∧ y = y₂ + t * (y₃ - y₂)) ↔
      (!![1, 1, 1; x, x₂, x₃; y, y₂, y₃] : Matrix (Fin 3) (Fin 3) ℝ).det = 0 := by
  Hint "Expand the determinant first: it says $x_2y_3 - x_3y_2 - xy_3 + x_3y + xy_2 - x_2y = 0$."
  Hint (hidden := true) "`rw [Matrix.det_fin_three]` and `simp`, then `constructor`."
  rw [Matrix.det_fin_three]
  simp
  constructor
  · Hint (hidden := true) "`intro ⟨t, hx, hy⟩`, `rw [hx, hy]`, `ring`."
    intro ⟨t, hx, hy⟩
    rw [hx, hy]
    ring
  · intro h
    Hint "Which of $x_3 - x_2$, $y_3 - y_2$ can you divide by? Use it to find $t$."
    Hint (hidden := true) "`rcases hBC with hx | hy`. If $x_2 \\ne x_3$, take
    `t = (x - x₂) / (x₃ - x₂)`."
    rcases hBC with hx | hy
    · have hx' : x₃ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
      use (x - x₂) / (x₃ - x₂)
      constructor
      · field_simp
        ring
      · field_simp
        linear_combination h
    · have hy' : y₃ - y₂ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
      use (y - y₂) / (y₃ - y₂)
      constructor
      · field_simp
        linear_combination -h
      · field_simp
        ring

end LinearAlgebraGame

Conclusion "$P$ is on the line $BC$ exactly when the triangle $PBC$ has zero area."

NewTheorem sub_ne_zero
TheoremTab "Det"
