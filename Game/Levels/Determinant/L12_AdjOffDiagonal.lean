import Game.Levels.Determinant.L11_Columns

World "Determinant"
Level 12
Title "The adjoint of a diagonal matrix, off the diagonal"

Introduction "
Sheet 9 Q4 asks for the adjoint of a diagonal matrix $D = \\operatorname{diag}(v_1, \\dots, v_n)$.
We take it in two steps; first the entries **off** the diagonal.

Lean's `Matrix.adjugate` is Hefferon's adjoint. Mathlib describes its $(i,j)$ entry as the
determinant of $D$ with row $j$ replaced by the unit vector $\\vec e_i$
(`Matrix.adjugate_apply`; the unit vector is `Pi.single i 1`) — by Laplace expansion along
that row this is exactly the cofactor.

Useful: `Matrix.updateRow_self` (the replaced row), `Matrix.updateRow_ne` (the other rows),
`Matrix.diagonal_apply_ne` (off-diagonal entries of `diagonal v` are $0$),
`Pi.single_eq_of_ne'` (the unit vector $\\vec e_i$ is $0$ away from position $i$) and
`Matrix.det_eq_zero_of_column_eq_zero`.
"

namespace LinearAlgebraGame

open Matrix in
/-- Off the diagonal, the adjoint of a diagonal matrix is zero. -/
Statement adjugate_diagonal_ne {n : ℕ} (v : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    adjugate (diagonal v) i j = 0 := by
  Hint "Look at column $j$ of the modified matrix: row $j$ is $\\vec e_i$, whose $j$-th entry is
  $0$ since $i \\ne j$; every other row is a row of $D$, whose $j$-th entry is off the
  diagonal. So column $j$ is zero."
  Hint (hidden := true) "`rw [adjugate_apply]`, then `apply det_eq_zero_of_column_eq_zero j`
  and `intro k`."
  rw [adjugate_apply]
  apply det_eq_zero_of_column_eq_zero j
  intro k
  Hint (hidden := true) "`by_cases hk : k = j`. In row $j$ the entry is `Pi.single i 1 j`;
  elsewhere it is an off-diagonal entry of `diagonal v`."
  by_cases hk : k = j
  · Hint (hidden := true) "`rw [hk, updateRow_self, Pi.single_eq_of_ne' hij]`."
    rw [hk, updateRow_self, Pi.single_eq_of_ne' hij]
  · Hint (hidden := true) "`rw [updateRow_ne hk, diagonal_apply_ne _ hk]`."
    rw [updateRow_ne hk, diagonal_apply_ne _ hk]

end LinearAlgebraGame

Conclusion "Off the diagonal the cofactor's matrix has a zero column, so the entry is $0$."

NewTheorem Matrix.adjugate_apply Matrix.diagonal_apply_ne Matrix.det_eq_zero_of_column_eq_zero Matrix.updateRow_self Matrix.updateRow_ne Pi.single_eq_of_ne'
NewDefinition Matrix.adjugate
DisabledTheorem Matrix.adjugate_diagonal
DisabledTactic simp norm_num
TheoremTab "Det"
