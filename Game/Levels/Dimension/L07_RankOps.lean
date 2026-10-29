import Game.Levels.Dimension.L06_RankLe

World "Dimension"
Level 7
Title "Rank of −A, kA, A + B"

-- @sheet 4 Q11
/-! @answer
The rank is the dimension of the column space.
**$\operatorname{rank}(-A) = \operatorname{rank} A$**: the columns of $-A$ are the negatives
of those of $A$, so each column space is inside the other.
**$\operatorname{rank}(kA) = \operatorname{rank} A$ for $k \neq 0$, and $= 0$ for $k = 0$**:
for $k\ne0$ the columns of $kA$ are multiples of those of $A$ and vice versa (multiply by
$k^{-1}$); $0\cdot A$ is the zero matrix.
**$\operatorname{rank}(A+B) \le \operatorname{rank} A + \operatorname{rank} B$**: each column
of $A+B$ is (column of $A$) + (column of $B$), so
$\operatorname{colspace}(A+B) \subseteq \operatorname{colspace}A + \operatorname{colspace}B$;
by Q10(a) and $\dim(U+W) \le \dim U + \dim W$ the claim follows. (Equality can fail:
$B = -A$.)
-/
Introduction "
**Problem Sheet 4, Question 11.** What is the relationship between $\\operatorname{rank}(A)$ and
$\\operatorname{rank}(-A)$? Between $\\operatorname{rank}(A)$ and $\\operatorname{rank}(kA)$? What,
if any, is the relationship between $\\operatorname{rank}(A)$, $\\operatorname{rank}(B)$, and
$\\operatorname{rank}(A + B)$? *Hint: Use Question 10.*

Work out the relationships on paper first; the claim below is what you should find. Your tool
is `rank_le_of_cols_mem` from the last level, together with the column rules `col_neg`,
`col_smul`, `col_add` (e.g. `(k • A).col j = k • A.col j`). A column of $C$ is in its own column
space: `Submodule.subset_span ⟨j, rfl⟩`.
"

namespace LinearAlgebraGame

open Matrix

/-- $\operatorname{rank}(-A) = \operatorname{rank}A$; $\operatorname{rank}(kA)$ is $0$ if $k = 0$ and
$\operatorname{rank}A$ otherwise; $\operatorname{rank}(A+B) \le \operatorname{rank}A +
\operatorname{rank}B$. -/
Statement {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (k : ℝ) :
    (-A).rank = A.rank ∧ (k = 0 → (k • A).rank = 0) ∧ (k ≠ 0 → (k • A).rank = A.rank) ∧
    (A + B).rank ≤ A.rank + B.rank := by
  Hint "Four claims: `refine ⟨?_, ?_, ?_, ?_⟩`."
  refine ⟨?_, ?_, ?_, ?_⟩
  · Hint "Two inequalities: each column of one is minus a column of the other."
    apply le_antisymm
    · apply rank_le_of_cols_mem
      intro j
      Hint (hidden := true) "`rw [col_neg]`, then `exact Submodule.neg_mem _ (Submodule.subset_span ⟨j, rfl⟩)`."
      rw [col_neg]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    · apply rank_le_of_cols_mem
      intro j
      Hint (hidden := true) "Column $j$ of $A$ is $-(-A).col\\ j$: `rw [← neg_neg (A.col j), ← col_neg]`."
      rw [← neg_neg (A.col j), ← col_neg]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hk
    Hint (hidden := true) "`rw [{hk}, zero_smul]`, then `exact rank_zero`."
    rw [hk, zero_smul]
    exact rank_zero
  · Hint "For $k \\ne 0$: columns of $kA$ are $k$ times columns of $A$, and back by dividing by $k$."
    intro hk
    apply le_antisymm
    · apply rank_le_of_cols_mem
      intro j
      rw [col_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · apply rank_le_of_cols_mem
      intro j
      Hint (hidden := true) "`have h : A.col j = k⁻¹ • (k • A).col j := by
      rw [col_smul, smul_smul, inv_mul_cancel₀ {hk}, one_smul]`"
      have h : A.col j = k⁻¹ • (k • A).col j := by
        rw [col_smul, smul_smul, inv_mul_cancel₀ hk, one_smul]
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · Hint "colspace$(A+B) \\subseteq$ colspace$A$ + colspace$B$, then Question 10(a) and
    $\\dim(U + W) \\le \\dim U + \\dim W$."
    Hint (hidden := true) "`Submodule.finrank_add_le_finrank_add_finrank` is the last inequality."
    rw [rank_eq_finrank_span_cols, rank_eq_finrank_span_cols A, rank_eq_finrank_span_cols B]
    have hle : Submodule.span ℝ (Set.range (A + B).col) ≤
        Submodule.span ℝ (Set.range A.col) ⊔ Submodule.span ℝ (Set.range B.col) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [col_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨j, rfl⟩) (Submodule.subset_span ⟨j, rfl⟩)
    have h1 := finrank_le_of_le _ _ hle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span ℝ (Set.range A.col)) (Submodule.span ℝ (Set.range B.col))
    omega

end LinearAlgebraGame

Conclusion "
$\\operatorname{rank}(-A) = \\operatorname{rank}A$; $\\operatorname{rank}(kA) = \\operatorname{rank}A$
for $k\\neq0$ (and $0$ for $k=0$); $\\operatorname{rank}(A+B)\\le\\operatorname{rank}A+\\operatorname{rank}B$
(equality can fail: take $B = -A$).
"

TheoremTab "Rank"
NewTheorem LinearAlgebraGame.rank_le_of_cols_mem LinearAlgebraGame.col_neg LinearAlgebraGame.col_smul LinearAlgebraGame.col_add Submodule.add_mem_sup Submodule.finrank_add_le_finrank_add_finrank Submodule.neg_mem neg_neg
