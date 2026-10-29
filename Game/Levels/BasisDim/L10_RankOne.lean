import Game.Levels.BasisDim.L09_RankZero

World "BasisDim"
Level 10
Title "Rank one"

-- @sheet 3 Q9
/-! @answer
**Rank 0: only the zero matrix** (rank = dimension of the column space, which is $\{\vec 0\}$
iff every column is $\vec 0$).
**Rank 1: exactly the nonzero matrices whose columns are all multiples of one vector**
(equivalently, all rows are multiples of a single row): $A = \vec u\,\vec v^{\,T}$ with
$\vec u, \vec v \neq \vec 0$, i.e. $a_{ij} = u_i v_j$. Indeed if the column space is the
line $[\{\vec u\}]$, column $j$ is $v_j\vec u$; conversely every column of $\vec u\vec v^{\,T}$
lies in $[\{\vec u\}]$, so the rank is at most 1, and it is not 0 when the matrix is nonzero.
-/
Introduction "
**Problem Sheet 3, Question 9** (rank one). Which matrices have rank one? No proof required.

Again an *explain level*: write your description in a comment starting `-- Explain:`.
Here `vecMulVec u v` is the matrix $\\vec u\\,\\vec v^{\\,T}$ with entries $u_i v_j$
(`vecMulVec_apply`); its column $j$ is $v_j\\vec u$.

Tools: `rank_eq_zero_iff` (rank 0, last level), `Submodule.finrank_mono` (a subspace of
$W$ has dimension $\\le \\dim W$ — Hefferon's result; Sheet 4 Q10(a) asks you to prove it later),
`finrank_span_singleton_le_one` (a line has dimension $\\le 1$) and
`exists_line_of_finrank_eq_one`: a one-dimensional subspace $W$ contains a nonzero $\\vec u$
such that every $\\vec w \\in W$ is a multiple $c\\,\\vec u$.

**New:** `choose f hf using h` turns `h : ∀ x, ∃ y, P x y` into a function `f` with
`hf : ∀ x, P x (f x)`.

**New:** `omega` proves (in)equalities about natural numbers (and integers) that follow from the
hypotheses by adding and comparing — handy for juggling dimensions.
"

namespace LinearAlgebraGame

open Matrix

/-- Rank 1 iff $A \neq 0$ and $A = \vec u\,\vec v^{\,T}$. -/
Statement {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank = 1 ↔ A ≠ 0 ∧ ∃ u : Fin m → ℝ, ∃ v : Fin n → ℝ, A = vecMulVec u v := by
  -- Explain: rank 1 means the column space is a line [u], so every column is a multiple
  -- of u: A = u vᵀ with u, v nonzero (equivalently all rows are multiples of one row).
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · Hint "If $A = 0$, what is its rank?"
      intro hA
      Hint (hidden := true) "`rw [{hA}, rank_zero] at {h}`, then `norm_num at {h}`."
      rw [hA, rank_zero] at h
      norm_num at h
    · Hint "A 1-dimensional column space is a line: there is a vector
      $u$ such that every column is a multiple of $u$."
      Hint (hidden := true) "`rw [rank_eq_finrank_span_cols] at {h}`, then
      `obtain ⟨u, -, -, hu⟩ := exists_line_of_finrank_eq_one {h}`."
      rw [rank_eq_finrank_span_cols] at h
      obtain ⟨u, -, -, hu⟩ := exists_line_of_finrank_eq_one h
      Hint "Each column is in the column space, so it is a multiple of $u$."
      Hint (hidden := true) "`have hc : ∀ j, ∃ c : ℝ, c • u = A.col j := fun j =>
      {hu} (A.col j) (Submodule.subset_span ⟨j, rfl⟩)`"
      have hc : ∀ j, ∃ c : ℝ, c • u = A.col j := fun j =>
        hu (A.col j) (Submodule.subset_span ⟨j, rfl⟩)
      Hint "Collect the multiples into one vector $v$ with `choose`."
      Hint (hidden := true) "`choose v hv using {hc}`"
      choose v hv using hc
      refine ⟨u, v, ?_⟩
      Hint (hidden := true) "`ext i j`, `have := congrFun ({hv} j) i`, then
      `rw [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this` and
      `rw [vecMulVec_apply, ← this, mul_comm]`."
      ext i j
      have := congrFun (hv j) i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
      rw [vecMulVec_apply, ← this, mul_comm]
  · rintro ⟨hA, u, v, huv⟩
    Hint "Every column of $u v^T$ lies in the line through $u$, so the rank is
    at most 1; and it is not 0 because $A \\ne 0$."
    rw [huv] at hA
    rw [huv]
    have h3 : (vecMulVec u v).rank ≠ 0 := by
      Hint (hidden := true) "`intro h`, then `exact {hA} ((rank_eq_zero_iff _).mp h)`."
      intro h
      exact hA ((rank_eq_zero_iff _).mp h)
    Hint (hidden := true) "`have hle : Submodule.span ℝ (Set.range (vecMulVec u v).col) ≤
    Submodule.span ℝ {u}`: by `rw [Submodule.span_le]` it is enough that each column is a
    multiple of $u$ (`Submodule.mem_span_singleton`)."
    have hle : Submodule.span ℝ (Set.range (vecMulVec u v).col) ≤ Submodule.span ℝ {u} := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      use v j
      ext i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.col_apply, vecMulVec_apply, mul_comm]
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_span_singleton_le_one u
    rw [rank_eq_finrank_span_cols] at h3 ⊢
    Hint (hidden := true) "Model explanation: *rank 1: the nonzero matrices $u v^T$ — all
    columns are multiples of one nonzero vector, equivalently all rows are multiples of a
    single row.* Finish with `omega`."
    omega

end LinearAlgebraGame

Conclusion "
**Rank 0:** only the zero matrix. **Rank 1:** the nonzero matrices $\\vec u\\vec v^{\\,T}$
(all rows multiples of a single row).
"

TheoremTab "Rank"

NewTactic choose omega
NewTheorem Submodule.finrank_mono LinearAlgebraGame.rank_eq_zero_iff LinearAlgebraGame.exists_line_of_finrank_eq_one LinearAlgebraGame.finrank_span_singleton_le_one Matrix.vecMulVec_apply Matrix.col_apply Matrix.rank_zero
NewDefinition Matrix.vecMulVec
