import Game.Levels.BasisDim.L08_Exchange

World "BasisDim"
Level 9
Title "Rank zero"

-- @sheet 3 Q9
/-! @answer
**Rank 0: only the zero matrix.** The rank is the dimension of the column space, and a space
has dimension 0 iff it is $\{\vec 0\}$; the span of the columns is $\{\vec 0\}$ iff every
column is $\vec 0$, i.e. iff $A = 0$.
-/
Introduction "
**Problem Sheet 3, Question 9.** Which matrices have rank zero? Rank one? No proof required.

This level: rank zero; the rank-one half is the next level. It is an *explain level*: the
sheet asks for a description, and Lean checks that your description is right. Inside your
proof, also write your description in words as a comment starting `-- Explain:` — it goes
into your hand-in.

The **rank** of $A$, `A.rank`, is the dimension of its column space: `rank_eq_finrank_span_cols`
says `A.rank = finrank ℝ (span ℝ (Set.range A.col))`, where `A.col j` is column $j$.
A space has dimension $0$ exactly when it is the trivial space `⊥`.
"

namespace LinearAlgebraGame

open Matrix

/-- A matrix has rank $0$ iff it is the zero matrix. -/
Statement rank_eq_zero_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : A.rank = 0 ↔ A = 0 := by
  -- Explain: rank 0 means the column space is {0}, i.e. every column is 0: only the zero matrix.
  Hint "The column space is the zero space exactly when every column is $\\vec 0$. Turn the rank
  into a statement about the columns."
  Hint (hidden := true) "`rw [rank_eq_finrank_span_cols, Submodule.finrank_eq_zero,
  Submodule.span_eq_bot, Set.forall_mem_range]`"
  rw [rank_eq_finrank_span_cols, Submodule.finrank_eq_zero, Submodule.span_eq_bot,
    Set.forall_mem_range]
  constructor
  · Hint "Every column is zero, so every entry is zero."
    intro h
    Hint (hidden := true) "`ext i j`, then entry $(i, j)$ is entry $i$ of column $j$:
    `exact congrFun ({h} j) i`."
    ext i j
    exact congrFun (h j) i
  · intro h j
    Hint (hidden := true) "`rw [{h}]`; column $j$ of the zero matrix is zero by definition:
    `exact rfl`."
    rw [h]
    Hint (hidden := true) "Model explanation: *rank 0 means the column space is the zero space,
    so every column is $\\vec 0$: only the zero matrix has rank 0.*"
    exact rfl

end LinearAlgebraGame

Conclusion "
**Rank 0:** only the zero matrix. `rank_eq_zero_iff` is in your inventory for the rank-one
half.
"

TheoremTab "Rank"

NewTheorem Submodule.span_eq_bot Set.forall_mem_range Matrix.rank_eq_finrank_span_cols Submodule.finrank_eq_zero
NewDefinition Matrix.col Matrix.rank Module.finrank
