import Game.Metadata
import Game.Ch3b

World "MatrixAlgebra"
Level 1
Title "Triangular times triangular"

-- @sheet 7 Q4
/-! @answer
Let $G, H$ be upper triangular and $i > j$. Then $(GH)_{ij} = \sum_k g_{ik}h_{kj}$. For each $k$:
if $k < i$ then $g_{ik} = 0$; otherwise $k \ge i > j$ and $h_{kj} = 0$. So every term vanishes
and $(GH)_{ij} = 0$: $GH$ is upper triangular. **Yes, the same holds for lower triangular
matrices**: either repeat the argument with the inequalities reversed, or transpose
($(GH)^{\mathsf T} = H^{\mathsf T}G^{\mathsf T}$ and transposes swap upper and lower).
-/
Introduction "
**Problem Sheet 7, Question 4.** A square matrix is *upper triangular* if its only nonzero
entries lie above, or on, the diagonal. Show that the product of two upper triangular matrices
is upper triangular. Does this hold for lower triangular also?

`IsUpperTri A` means `∀ i j, j < i → A i j = 0`; `IsLowerTri A` means
`∀ i j, i < j → A i j = 0`. The goal has two parts: prove the upper-triangular claim, then
decide the lower-triangular question (`left`: it can fail, `right`: it holds) and prove your answer.
"

namespace LinearAlgebraGame

/-- Upper triangular matrices are closed under products; and are lower triangular ones? -/
Statement {n : ℕ} :
    (∀ G H : Matrix (Fin n) (Fin n) ℝ, IsUpperTri G → IsUpperTri H → IsUpperTri (G * H)) ∧
    ((¬ ∀ G H : Matrix (Fin n) (Fin n) ℝ, IsLowerTri G → IsLowerTri H → IsLowerTri (G * H)) ∨
     (∀ G H : Matrix (Fin n) (Fin n) ℝ, IsLowerTri G → IsLowerTri H → IsLowerTri (G * H))) := by
  constructor
  · Hint "Take an entry below the diagonal ($j < i$) and show every term
    $g_\{ik}h_\{kj}$ of the sum is zero: either $k < i$ or $k \\ge i > j$."
    intro G H hG hH i j hji
    Hint (hidden := true) "`rw [Matrix.mul_apply]`, `apply Finset.sum_eq_zero`, `intro k _`,
    then `by_cases hk : k < i`."
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k < i
    · rw [hG i k hk, zero_mul]
    · Hint (hidden := true) "`rw [{hH} k j (by omega), mul_zero]`"
      rw [hH k j (by omega), mul_zero]
  · Hint "Decide. Does the same argument work with the inequalities reversed?"
    right
    intro G H hG hH i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i < k
    · rw [hG i k hk, zero_mul]
    · rw [hH k j (by omega), mul_zero]

end LinearAlgebraGame

Conclusion "
**Yes** for lower triangular too: every term $g_{ik}h_{kj}$ with $i < j$ has $i < k$ or $k < j$.
"

NewDefinition LinearAlgebraGame.IsUpperTri LinearAlgebraGame.IsLowerTri
DisabledTheorem Matrix.BlockTriangular.mul Matrix.upper_two_blockTriangular
TheoremTab "Matrices"
NewTheorem Finset.sum_eq_zero MulZeroClass.zero_mul
