import Game.Levels.Dimension.L03_Meet

World "Dimension"
Level 4
Title "Row rank equals column rank"

Introduction "
**Theorem Two.III.3.11:** the row rank of a matrix equals its column rank. Hefferon proves it
by row reduction; here it is granted as `Matrix.rank_transpose`: $\\operatorname{rank} A^T =
\\operatorname{rank} A$ (the rows of $A$ are the columns of $A^T$).

Use it: an $m\\times n$ matrix has rank at most $m$. You already know rank $\\le n$
(`Matrix.rank_le_width`: at most $n$ columns). Apply that to $A^T$.
"

namespace LinearAlgebraGame

open Matrix

/-- An $m \times n$ matrix has rank at most $m$. -/
Statement {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : A.rank ≤ m := by
  Hint "Rows of $A$ are columns of $A^T$."
  Hint (hidden := true) "`rw [← rank_transpose]` then `exact rank_le_width Aᵀ`."
  rw [← rank_transpose]
  exact rank_le_width Aᵀ

end LinearAlgebraGame

Conclusion "
So $\\operatorname{rank} A \\le \\min(m, n)$.
"

NewTheorem Matrix.rank_transpose Matrix.rank_le_width
DisabledTheorem Matrix.rank_le_height Matrix.rank_le_card_height
DisabledTactic simp norm_num
TheoremTab "Rank"
