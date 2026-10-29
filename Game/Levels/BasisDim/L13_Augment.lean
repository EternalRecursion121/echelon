import Game.Levels.BasisDim.L12_RankOne

World "BasisDim"
Level 13
Title "The columns of [A | b]"

Introduction "
To talk about the *augmented matrix* $[A \\mid b]$ we need it as a matrix: `augment A b`
is the $m \\times (n+1)$ matrix whose first $n$ columns are those of $A$ and whose last column
is $\\vec b$.

Prove the bridge: the rank of $[A \\mid b]$ is the dimension of the span of the columns of
$A$ **together with** $\\vec b$.

`augment_col` describes the columns of $[A\\mid b]$: they are `Fin.snoc A.col b`, the columns
of $A$ with $\\vec b$ appended at the end.
"

namespace LinearAlgebraGame

open Matrix

/-- $\operatorname{rank}[A \mid b] = \dim [\{\vec b\} \cup \text{columns of } A]$. -/
Statement rank_augment {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (augment A b).rank = Module.finrank ℝ (Submodule.span ℝ (insert b (Set.range A.col))) := by
  Hint "Rewrite the rank as the dimension of a column span, then identify the columns."
  Hint (hidden := true) "`Fin.range_snoc` says the set of entries of `Fin.snoc f x` is
  `insert x (Set.range f)`."
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
