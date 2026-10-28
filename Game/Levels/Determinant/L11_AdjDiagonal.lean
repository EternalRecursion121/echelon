import Game.Levels.Determinant.L10_Columns

World "Determinant"
Level 11
Title "The adjoint of a diagonal matrix"

-- @sheet 9 Q4
/-! @answer
For $D = \operatorname{diag}(d_1,\dots,d_n)$,
$$\operatorname{adj}(D) = \operatorname{diag}\Big(\prod_{j\ne 1} d_j,\ \dots,\ \prod_{j \ne n} d_j\Big).$$
The $(i,j)$ entry of $\operatorname{adj}(D)$ is the cofactor $D_{j,i} = (-1)^{i+j}$ times the
minor obtained by deleting row $j$ and column $i$. If $i \ne j$, that minor still contains
row $i$ of $D$ with its only nonzero entry deleted, so it has a zero row and is $0$. If
$i = j$, deleting row and column $i$ leaves $\operatorname{diag}(d_1,\dots,\widehat{d_i},\dots,d_n)$,
with determinant $\prod_{j\ne i} d_j$. (Check: if $D$ is invertible, $\operatorname{adj}(D) = \det(D)\,D^{-1}$.)
-/
Introduction "
**Problem Sheet 9, Question 4.** Give a formula for the adjoint of a diagonal matrix.

**Answer to prove:** $\\operatorname{adj}(\\operatorname{diag}(d_1,\\dots,d_n)) =
\\operatorname{diag}(\\prod_{j\\ne 1} d_j, \\dots, \\prod_{j\\ne n} d_j)$.

Lean's `Matrix.adjugate` is Hefferon's adjoint. Mathlib describes its $(i,j)$ entry as the
determinant of $D$ with row $j$ replaced by the unit vector $e_i$ (`Matrix.adjugate_apply`)
— by Laplace expansion along that row this is exactly the cofactor.
`Finset.univ.erase i` is the index set $\\{1,\\dots,n\\} \\setminus \\{i\\}$.
"

namespace LinearAlgebraGame

open Matrix in
/-- $\operatorname{adj}(\operatorname{diag}(v)) = \operatorname{diag}(i \mapsto \prod_{j \ne i} v_j)$. -/
Statement {n : ℕ} (v : Fin n → ℝ) :
    adjugate (diagonal v) = diagonal fun i => ∏ j ∈ Finset.univ.erase i, v j := by
  Hint "Compare entries. Off the diagonal, the modified matrix has a zero column; on the
  diagonal it is again diagonal, with $v_i$ replaced by $1$."
  Hint (hidden := true) "`ext i j`, `rw [adjugate_apply]`, then `by_cases hij : i = j`."
  ext i j
  rw [adjugate_apply]
  by_cases hij : i = j
  · Hint (hidden := true) "`rw [← hij, diagonal_apply_eq, diagonal_updateRow_single, det_diagonal]`,
    then `Finset.prod_update_of_mem (Finset.mem_univ i)`, `Finset.sdiff_singleton_eq_erase`, `one_mul`."
    rw [← hij, diagonal_apply_eq, diagonal_updateRow_single, det_diagonal,
      Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase, one_mul]
  · Hint (hidden := true) "`rw [diagonal_apply_ne _ hij]`, then
    `apply det_eq_zero_of_column_eq_zero j`: show column $j$ is zero."
    rw [diagonal_apply_ne _ hij]
    apply det_eq_zero_of_column_eq_zero j
    intro k
    Hint (hidden := true) "`by_cases hk : k = j`. In row $j$ the entry is `Pi.single i 1 j`;
    elsewhere it is an off-diagonal entry of `diagonal v`."
    by_cases hk : k = j
    · rw [hk, updateRow_self, Pi.single_apply, if_neg (Ne.symm hij)]
    · rw [updateRow_ne hk, diagonal_apply_ne _ hk]

end LinearAlgebraGame

Conclusion "
So the adjoint of a diagonal matrix is diagonal, with $i$-th entry the product of all the
*other* diagonal entries.
"

NewTheorem Matrix.adjugate_apply Matrix.diagonal_apply_eq Matrix.diagonal_apply_ne Matrix.diagonal_updateRow_single Matrix.det_diagonal Finset.prod_update_of_mem Finset.sdiff_singleton_eq_erase one_mul Matrix.det_eq_zero_of_column_eq_zero Matrix.updateRow_self Matrix.updateRow_ne if_neg
NewDefinition Matrix.adjugate
DisabledTheorem Matrix.adjugate_diagonal
DisabledTactic simp norm_num
TheoremTab "Det"
