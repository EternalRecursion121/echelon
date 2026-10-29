import Game.Levels.Determinant.L12_AdjOffDiagonal

World "Determinant"
Level 13
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

You know the off-diagonal entries are $0$ (`adjugate_diagonal_ne`). On the diagonal, entry
$(i,i)$ is the determinant of $D$ with row $i$ replaced by $\\vec e_i$ — again a diagonal
matrix (`Matrix.diagonal_updateRow_single`), whose determinant is the product of its diagonal
(`Matrix.det_diagonal`).

**Find the formula** in the form: entry $(i,i)$ of $\\operatorname{adj}(D)$ is a product
$\\prod_{j \\in S_i} v_j$ over some index set $S_i$ that you choose. Some notation:
`Finset.univ` is $\\{1, \\dots, n\\}$, `s.erase i` is $s \\setminus \\{i\\}$, `{i}` is $\\{i\\}$.
Your set may depend on $n$ and $i$, but not on the entries $v$.

`Function.update v i 1` is $v$ with its $i$-th entry replaced by $1$;
`Finset.prod_update_of_mem` evaluates a product over such a vector.
"

namespace LinearAlgebraGame

open Matrix in
/-- There are index sets $S_i$ with $\operatorname{adj}(\operatorname{diag}(v)) = \operatorname{diag}(i \mapsto \prod_{j \in S_i} v_j)$ for every $n$ and every $v$. -/
Statement : ∃ S : (n : ℕ) → Fin n → Finset (Fin n), ∀ (n : ℕ) (v : Fin n → ℝ),
    adjugate (diagonal v) = diagonal fun i => ∏ j ∈ S n i, v j := by
  Hint "Which entries $v_j$ survive in the $(i,i)$ cofactor? Choose $S_i$, then compare the
  two matrices entry by entry."
  Hint (hidden := true) "The $(i,i)$ cofactor deletes row $i$ and column $i$, leaving
  $\\prod_\{j \\ne i} v_j$: `use fun n i => Finset.univ.erase i`, then `intro n v` and `ext i j`."
  use fun n i => Finset.univ.erase i
  intro n v
  ext i j
  Hint (hidden := true) "`by_cases hij : i = j`."
  by_cases hij : i = j
  · Hint (hidden := true) "`rw [← hij, diagonal_apply_eq, adjugate_apply, diagonal_updateRow_single, det_diagonal]`,
    then `Finset.prod_update_of_mem (Finset.mem_univ i)`, `Finset.sdiff_singleton_eq_erase`, `one_mul`."
    rw [← hij, diagonal_apply_eq, adjugate_apply, diagonal_updateRow_single, det_diagonal,
      Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase, one_mul]
  · Hint (hidden := true) "`rw [diagonal_apply_ne _ hij]` and the previous level."
    rw [diagonal_apply_ne _ hij]
    exact adjugate_diagonal_ne v hij

end LinearAlgebraGame

Conclusion "
So the adjoint of a diagonal matrix is diagonal, with $i$-th entry the product of all the
*other* diagonal entries.
"

NewTheorem LinearAlgebraGame.adjugate_diagonal_ne Matrix.diagonal_apply_eq Matrix.diagonal_updateRow_single Matrix.det_diagonal Finset.prod_update_of_mem Finset.sdiff_singleton_eq_erase one_mul
DisabledTheorem Matrix.adjugate_diagonal
DisabledTactic simp norm_num
TheoremTab "Det"
