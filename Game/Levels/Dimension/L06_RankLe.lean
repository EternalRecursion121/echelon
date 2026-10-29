import Game.Levels.Dimension.L05_RowCol

World "Dimension"
Level 6
Title "Fewer columns, smaller rank"

Introduction "
Sheet 4 Q11 (next level) compares the ranks of $A$, $-A$, $kA$ and $A + B$, with the hint
*use Question 10*. First the tool, Question 10(a) for column spaces: if every column of $D$
lies in the column space of $C$, then $\\operatorname{rank} D \\le \\operatorname{rank} C$.

Recall `rank_eq_finrank_span_cols`, your `finrank_le_of_le` (Mathlib's name for it,
`Submodule.finrank_mono`, has been in your inventory since the rank-one level), and `Submodule.span_le`: a span is
inside a subspace iff the generators are.
"

namespace LinearAlgebraGame

open Matrix

/-- If every column of $D$ is in the column space of $C$ then
$\operatorname{rank} D \le \operatorname{rank} C$. -/
Statement rank_le_of_cols_mem {m n : ℕ} (C D : Matrix (Fin m) (Fin n) ℝ)
    (hD : ∀ j, D.col j ∈ Submodule.span ℝ (Set.range C.col)) : D.rank ≤ C.rank := by
  Hint "Both ranks are dimensions of column spaces, and one column space sits inside the other."
  Hint (hidden := true) "`rw [rank_eq_finrank_span_cols, rank_eq_finrank_span_cols]`, then
  `apply finrank_le_of_le`."
  rw [rank_eq_finrank_span_cols, rank_eq_finrank_span_cols]
  apply finrank_le_of_le
  Hint "A span is inside a subspace if all its generators are."
  Hint (hidden := true) "`rw [Submodule.span_le]`, then `rintro _ ⟨j, rfl⟩`."
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hD j

end LinearAlgebraGame

Conclusion "
`rank_le_of_cols_mem` is in your inventory: to compare ranks, compare columns.
"

TheoremTab "Rank"
DisabledTactic simp norm_num
