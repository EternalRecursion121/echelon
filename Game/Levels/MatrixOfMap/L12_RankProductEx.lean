import Game.Levels.MatrixOfMap.L11_FiveMaps

World "MatrixOfMap"
Level 12
Title "Rank can drop in a product"

-- @sheet 8 Q2a
/-! @answer
Take $n = 1$ and the $2\times 2$ matrices $A = \begin{pmatrix}1&0\\0&0\end{pmatrix}$,
$B = \begin{pmatrix}0&0\\0&1\end{pmatrix}$. Each has rank $1$, but $AB = 0$ has rank $0 < 1$.
(Equally, the $1\times2$ matrix $(1\ 0)$ times the $2\times1$ matrix $(0\ 1)^{\mathsf T}$ is the
$1\times 1$ zero matrix.)
-/
Introduction "
**Problem Sheet 8, Question 2(a).** Find $n$ and two rank $n$ matrices whose product has rank
less than $n$.

Your matrices are $2\\times 2$. `Matrix.diagonal ![a, b]` is the diagonal matrix with
entries $a, b$, and `Matrix.rank_diagonal` says its rank is the number of nonzero entries.
"

namespace LinearAlgebraGame

/-- There are $n$ and two rank-$n$ matrices whose product has rank less than $n$. -/
Statement : ∃ n : ℕ, ∃ A B : Matrix (Fin 2) (Fin 2) ℝ,
    A.rank = n ∧ B.rank = n ∧ (A * B).rank < n := by
  Hint "Look for two nonzero matrices whose product is zero. Diagonal ones are easiest."
  Hint (hidden := true) "`use 1, Matrix.diagonal ![1, 0], Matrix.diagonal ![0, 1]`"
  use 1, Matrix.diagonal ![1, 0], Matrix.diagonal ![0, 1]
  Hint (hidden := true) "For each rank: `rw [Matrix.rank_diagonal, Fintype.card_subtype,
  Finset.card_filter, Fin.sum_univ_two]` and `simp`. For the product first
  `rw [Matrix.diagonal_mul_diagonal]`."
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_two]
    simp
  · rw [Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_two]
    simp
  · rw [Matrix.diagonal_mul_diagonal, Matrix.rank_diagonal, Fintype.card_subtype,
      Finset.card_filter, Fin.sum_univ_two]
    simp

end LinearAlgebraGame

Conclusion "
$n = 1$: $\\mathrm{diag}(1,0)\\cdot\\mathrm{diag}(0,1) = 0$.
"

TheoremTab "Matrices"
NewDefinition Matrix.diagonal
NewTheorem Matrix.rank_diagonal Fintype.card_subtype Finset.card_filter Matrix.diagonal_mul_diagonal
