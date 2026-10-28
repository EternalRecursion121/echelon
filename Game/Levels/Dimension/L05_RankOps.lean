import Game.Levels.Dimension.L04_RowCol

World "Dimension"
Level 5
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

The statement records the answers. A good first step is a general lemma as a `have`: if every
column of $D$ is in the column space of $C$, then $\\operatorname{rank} D \\le \\operatorname{rank} C$
(Question 10(a) for column spaces).
"

namespace LinearAlgebraGame

open Matrix

/-- $\operatorname{rank}(-A) = \operatorname{rank}A$; $\operatorname{rank}(kA)$ is $0$ if $k = 0$ and
$\operatorname{rank}A$ otherwise; $\operatorname{rank}(A+B) \le \operatorname{rank}A +
\operatorname{rank}B$. -/
Statement {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (k : ℝ) :
    (-A).rank = A.rank ∧ (k = 0 → (k • A).rank = 0) ∧ (k ≠ 0 → (k • A).rank = A.rank) ∧
    (A + B).rank ≤ A.rank + B.rank := by
  Hint "First the general lemma: columns of $D$ inside the column space of $C$ ⇒
  $rank D \\le rank C$."
  have key : ∀ C D : Matrix (Fin m) (Fin n) ℝ,
      (∀ j, D.col j ∈ Submodule.span ℝ (Set.range C.col)) → D.rank ≤ C.rank := by
    intro C D hD
    rw [rank_eq_finrank_span_cols, rank_eq_finrank_span_cols]
    apply Submodule.finrank_mono
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hD j
  have mem : ∀ (C : Matrix (Fin m) (Fin n) ℝ) j, C.col j ∈ Submodule.span ℝ (Set.range C.col) :=
    fun C j => Submodule.subset_span ⟨j, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · Hint "Two inequalities: each column of one is minus a column of the other."
    apply le_antisymm
    · apply key
      intro j
      have : (-A).col j = -(A.col j) := rfl
      rw [this]
      exact Submodule.neg_mem _ (mem A j)
    · apply key
      intro j
      have : A.col j = -((-A).col j) := by ext i; simp
      rw [this]
      exact Submodule.neg_mem _ (mem _ j)
  · intro hk
    rw [hk, zero_smul]
    exact rank_zero
  · Hint "For $k \\ne 0$: columns of $kA$ are $k$ times columns of $A$, and back by dividing by $k$."
    intro hk
    apply le_antisymm
    · apply key
      intro j
      have : (k • A).col j = k • A.col j := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (mem A j)
    · apply key
      intro j
      have : A.col j = k⁻¹ • (k • A).col j := by ext i; simp [hk]
      rw [this]
      exact Submodule.smul_mem _ _ (mem _ j)
  · Hint "colspace$(A+B) \\subseteq$ colspace$A$ + colspace$B$, then Question 10(a) and
    $\\dim(U + W) \\le \\dim U + \\dim W$."
    Hint (hidden := true) "`Submodule.finrank_add_le_finrank_add_finrank` is the last inequality."
    rw [rank_eq_finrank_span_cols, rank_eq_finrank_span_cols A, rank_eq_finrank_span_cols B]
    have hle : Submodule.span ℝ (Set.range (A + B).col) ≤
        Submodule.span ℝ (Set.range A.col) ⊔ Submodule.span ℝ (Set.range B.col) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.add_mem_sup (mem A j) (mem B j)
    exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

end LinearAlgebraGame

Conclusion "
$\\operatorname{rank}(-A) = \\operatorname{rank}A$; $\\operatorname{rank}(kA) = \\operatorname{rank}A$
for $k\\neq0$ (and $0$ for $k=0$); $\\operatorname{rank}(A+B)\\le\\operatorname{rank}A+\\operatorname{rank}B$.
"

TheoremTab "Rank"
NewTheorem Submodule.add_mem_sup Submodule.finrank_add_le_finrank_add_finrank Submodule.neg_mem
