import Game.Levels.BasisDim.L09_Augment

World "BasisDim"
Level 10
Title "Boss: when is a system solvable?"

-- @sheet 3 Q11
/-! @answer
Write $\vec c_1,\dots,\vec c_n$ for the columns of $A$. The system $A\vec x = \vec b$ says
$x_1\vec c_1 + \dots + x_n\vec c_n = \vec b$, so it has a solution iff $\vec b$ lies in the
column space $C = [\{\vec c_1,\dots,\vec c_n\}]$. The column space of $[A\mid b]$ is
$C' = [\{\vec c_1,\dots,\vec c_n,\vec b\}] \supseteq C$, and $\vec b \in C$ iff $C' = C$
(Lemma Two.II.1.2). Since $C \subseteq C'$ are finite-dimensional and nested, $C' = C$ iff
$\dim C' = \dim C$ (Sheet 4 Q10b). The rank of a matrix is the dimension of its column space,
so the system is solvable iff $\operatorname{rank} A = \operatorname{rank}[A\mid b]$.
-/
Introduction "
**Problem Sheet 3, Question 11.** Prove that a linear system has a solution if and only if
that system's matrix of coefficients has the same rank as its augmented matrix.

The chain of ideas:
1. $A\\vec x = \\vec b$ is solvable $\\iff$ $\\vec b$ is in the column space of $A$
   (`A *ᵥ x` is a combination of the columns; `Matrix.range_mulVecLin` says the range of
   $\\vec x \\mapsto A\\vec x$ is the column span);
2. $\\vec b \\in [S] \\iff [S \\cup \\{\\vec b\\}] = [S]$ (`Submodule.span_insert_eq_span`);
3. nested spans are equal $\\iff$ they have equal dimension (your Sheet 4 Q10b);
4. rank is the dimension of the column span (`rank_augment`).
"

namespace LinearAlgebraGame

open Matrix

/-- $A\vec x = \vec b$ has a solution iff $\operatorname{rank} A = \operatorname{rank}[A\mid b]$. -/
Statement {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x, A *ᵥ x = b) ↔ A.rank = (augment A b).rank := by
  Hint "Start by turning both ranks into dimensions of column spans."
  rw [rank_augment, rank_eq_finrank_span_cols]
  Hint "Step 1: solvable means $\\vec b$ is in the column span. Record it as a separate fact."
  have step1 : (∃ x, A *ᵥ x = b) ↔ b ∈ Submodule.span ℝ (Set.range A.col) := by
    Hint (hidden := true) "`rw [← Matrix.range_mulVecLin]` and the two sides agree by
    definition: `exact Iff.rfl`."
    rw [← Matrix.range_mulVecLin]
    exact Iff.rfl
  rw [step1]
  constructor
  · Hint "If $\\vec b$ is already in the span, adding it changes nothing."
    intro hb
    Hint (hidden := true) "`rw [Submodule.span_insert_eq_span {hb}]`"
    rw [Submodule.span_insert_eq_span hb]
  · intro hr
    Hint "The span without $\\vec b$ sits inside the span with $\\vec b$, and they have the
    same dimension. So they are equal (Sheet 4 Q10b) — and $\\vec b$ is in the bigger one."
    Hint (hidden := true) "`have he := (eq_iff_finrank_eq_of_le _ _ (Submodule.span_mono
    (Set.subset_insert b _))).mp {hr}`"
    have he := (eq_iff_finrank_eq_of_le _ _
      (Submodule.span_mono (Set.subset_insert b _))).mp hr
    rw [he]
    Hint (hidden := true) "`exact Submodule.subset_span (Set.mem_insert b _)`"
    exact Submodule.subset_span (Set.mem_insert b _)

end LinearAlgebraGame

Conclusion "
**Rouché–Capelli:** $A\\vec x = \\vec b$ is solvable iff
$\\operatorname{rank} A = \\operatorname{rank}[A \\mid b]$.
"

NewTheorem LinearAlgebraGame.rank_augment LinearAlgebraGame.eq_iff_finrank_eq_of_le Matrix.range_mulVecLin Submodule.span_insert_eq_span
DisabledTheorem Submodule.eq_of_le_of_finrank_eq
DisabledTactic simp norm_num
TheoremTab "Rank"
