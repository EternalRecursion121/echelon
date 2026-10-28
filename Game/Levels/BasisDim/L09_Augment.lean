import Game.Levels.BasisDim.L08_NestedEq

World "BasisDim"
Level 9
Title "The columns of [A | b]"

Introduction "
To talk about the *augmented matrix* $[A \\mid b]$ we need it as a matrix: `augment A b`
is the $m \\times (n+1)$ matrix whose first $n$ columns are those of $A$ and whose last column
is $\\vec b$.

The rank of a matrix is the dimension of the span of its columns
(`rank_eq_finrank_span_cols`). Prove the bridge: the column space of $[A \\mid b]$ is
spanned by the columns of $A$ **together with** $\\vec b$.

Useful: `augment_col` says the columns of $[A\\mid b]$ are `Fin.snoc A.col b`
(the columns of $A$ with $\\vec b$ appended), and `Fin.range_snoc` says the set of entries of
`Fin.snoc f x` is `insert x (Set.range f)`.
"

namespace LinearAlgebraGame

open Matrix

/-- $\operatorname{rank}[A \mid b] = \dim [\{\vec b\} \cup \text{columns of } A]$. -/
Statement rank_augment {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (augment A b).rank = Module.finrank ℝ (Submodule.span ℝ (insert b (Set.range A.col))) := by
  Hint "Rewrite the rank as the dimension of a column span, then identify the columns."
  Hint (hidden := true) "`rw [rank_eq_finrank_span_cols, augment_col, Fin.range_snoc]`"
  rw [rank_eq_finrank_span_cols, augment_col, Fin.range_snoc]

end LinearAlgebraGame

Conclusion "
Now `rank_augment` connects the rank of $[A\\mid b]$ to spans, where your dimension theory
lives.
"

NewDefinition LinearAlgebraGame.augment
NewTheorem LinearAlgebraGame.augment_col Fin.range_snoc
DisabledTactic simp norm_num
TheoremTab "Rank"
