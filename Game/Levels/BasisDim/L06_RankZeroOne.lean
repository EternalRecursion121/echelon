import Game.Levels.BasisDim.L05_ColSpace

World "BasisDim"
Level 6
Title "Rank zero, rank one"

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
**Problem Sheet 3, Question 9.** Which matrices have rank zero? Rank one? No proof required.

This is an *explain level*. The sheet asks for a description; Lean checks that your
description is right. Here `vecMulVec u v` is the matrix $\\vec u\\,\\vec v^{\\,T}$ with entries
$u_i v_j$. The rank of $A$ is the dimension of its column space
(`rank_eq_finrank_span_cols`).

Inside your proof, also write your description in words as a comment starting
`-- Explain:` — it goes into your hand-in.

**New:** `omega` proves (in)equalities about natural numbers and integers.

**New syntax:** `foo (h := e)` passes the argument named `h` explicitly, when a lemma has several arguments and you want to give just one of them.
"

namespace LinearAlgebraGame

open Matrix

/-- Rank 0 iff $A = 0$; rank 1 iff $A \neq 0$ and $A = \vec u\,\vec v^{\,T}$. -/
Statement {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (A.rank = 0 ↔ A = 0) ∧
    (A.rank = 1 ↔ A ≠ 0 ∧ ∃ u : Fin m → ℝ, ∃ v : Fin n → ℝ, A = vecMulVec u v) := by
  Hint "Rank 0 first: the column space is zero exactly when every column is zero.
  It is worth proving this as a separate fact, because the rank-1 part needs it too."
  have h0 : ∀ B : Matrix (Fin m) (Fin n) ℝ, B.rank = 0 ↔ B = 0 := by
    intro B
    Hint (hidden := true) "`rw [rank_eq_finrank_span_cols, Submodule.finrank_eq_zero,
    Submodule.span_eq_bot, Set.forall_mem_range]`"
    rw [rank_eq_finrank_span_cols, Submodule.finrank_eq_zero, Submodule.span_eq_bot,
      Set.forall_mem_range]
    constructor
    · intro h
      ext i j
      exact congrFun (h j) i
    · intro h j
      rw [h]
      exact rfl
  refine ⟨h0 A, ?_⟩
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hA
      rw [hA, rank_zero] at h
      omega
    · Hint "A 1-dimensional column space is a line: there is a vector
      $u$ such that every column is a multiple of $u$."
      Hint (hidden := true) "`finrank_eq_one_iff'` gives that $u$."
      rw [rank_eq_finrank_span_cols] at h
      obtain ⟨u, -, hu⟩ := finrank_eq_one_iff'.mp h
      have hc : ∀ j, ∃ c : ℝ, c • (u : Fin m → ℝ) = A.col j := by
        intro j
        obtain ⟨c, hc⟩ := hu ⟨A.col j, Submodule.subset_span ⟨j, rfl⟩⟩
        exact ⟨c, congrArg Subtype.val hc⟩
      Hint (hidden := true) "`choose v hv using {hc}` turns the multiples into a function
      $v$."
      choose v hv using hc
      refine ⟨u, v, ?_⟩
      ext i j
      have := congrFun (hv j) i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
      rw [vecMulVec_apply, ← this, mul_comm]
  · intro h
    obtain ⟨hA, u, v, huv⟩ := h
    Hint "Every column of $u v^T$ lies in the line through $u$, so the rank is
    at most 1; and it is not 0 by the first part."
    rw [huv] at hA
    rw [huv]
    have hle : Submodule.span ℝ (Set.range (vecMulVec u v).col) ≤ Submodule.span ℝ {u} := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨v j, by ext i; simp [vecMulVec_apply, mul_comm]⟩
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_span_le_card (R := ℝ) ({u} : Set (Fin m → ℝ))
    simp at h2
    have h3 : (vecMulVec u v).rank ≠ 0 := fun h => hA ((h0 _).mp h)
    rw [rank_eq_finrank_span_cols] at h3 ⊢
    -- Explain: rank 0 means the column space is {0}, so only the zero matrix.
    -- Rank 1 means the column space is a line [u], so every column is a multiple of u:
    -- A = u vᵀ with u, v nonzero (equivalently all rows are multiples of one row).
    Hint (hidden := true) "Model explanation: *rank 0: only the zero matrix. Rank 1: the
    nonzero matrices $u v^T$ — all columns are multiples of one nonzero vector,
    equivalently all rows are multiples of a single row.*"
    omega

end LinearAlgebraGame

Conclusion "
**Rank 0:** only the zero matrix. **Rank 1:** the nonzero matrices $\\vec u\\vec v^{\\,T}$
(all rows multiples of a single row).
"

TheoremTab "Rank"

NewTactic choose omega
NewTheorem Submodule.span_eq_bot Set.forall_mem_range Matrix.vecMulVec_apply Matrix.col_apply finrank_span_le_card Matrix.rank_eq_finrank_span_cols Submodule.finrank_eq_zero Matrix.rank_zero Submodule.finrank_mono finrank_eq_one_iff'
NewDefinition Matrix.vecMulVec Matrix.col Matrix.rank
