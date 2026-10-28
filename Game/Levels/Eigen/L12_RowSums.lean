import Game.Levels.Eigen.L11_DerivMult

World "Eigen"
Level 12
Title "Row sums"

-- @sheet 10 Q6a
/-! @answer
Let $\vec 1 = (1,\dots,1)^{\mathsf T} \ne \vec 0$. The $i$-th entry of $A\vec 1$ is the $i$-th row
sum $\sum_j a_{ij} = c$, so $A\vec 1 = c\vec 1$ and $c$ is an eigenvalue with eigenvector $\vec 1$.
-/
Introduction "
**Problem Sheet 10, Question 6** (first part). Show that if $A$ is an $n\\times n$ matrix
and each row sums to $c$, then $c$ is an eigenvalue.

(We write the size as $n+1$ so that the matrix is not empty: an empty matrix has no
eigenvectors.)
"

namespace LinearAlgebraGame

/-- If every row of $A$ sums to $c$ then $c$ is an eigenvalue of $A$. -/
Statement isEigenvalue_of_row_sums {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ)
    (h : ∀ i, ∑ j, A i j = c) : IsEigenvalue A c := by
  Hint "Which vector does a row sum come from? Try the all-ones vector."
  Hint (hidden := true) "`use fun _ => 1`, then `constructor`."
  use fun _ => 1
  constructor
  · Hint (hidden := true) "`intro h0`, `have := congrFun h0 0`, `simp at this`."
    intro h0
    have := congrFun h0 0
    simp at this
  · Hint (hidden := true) "`ext i` and `simp [Matrix.mulVec, dotProduct, h]`."
    ext i
    simp [Matrix.mulVec, dotProduct, h]

end LinearAlgebraGame

Conclusion "Eigenvector $(1, \\dots, 1)$. Stochastic matrices (rows summing to $1$) always have eigenvalue $1$."

TheoremTab "Eigen"
