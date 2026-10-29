import Game.Levels.Dimension.L09_SumInter

World "Dimension"
Level 10
Title "A sum"

-- @sheet 6 Q1a
/-! @answer
$W_1\cap W_2$: a matrix in both has first row $0$ and diagonal $0$, so it is
$\begin{pmatrix}0&0\\c&0\end{pmatrix}$: **$W_1\cap W_2 = \{\begin{pmatrix}0&0\\c&0\end{pmatrix}\}$,
basis $\langle E_{21}\rangle$, dimension 1.**
$W_1 + W_2 = \{\begin{pmatrix}0&0\\c&d\end{pmatrix} + \begin{pmatrix}0&b\\c'&0\end{pmatrix}\}
= \{\begin{pmatrix}0&b\\c&d\end{pmatrix}\}$ (all matrices with top-left entry 0):
**basis $\langle E_{12}, E_{21}, E_{22}\rangle$, dimension 3.**
(Check: $3 = 2 + 2 - 1$.)
-/
Introduction "
**Problem Sheet 6, Question 1(a), continued.** For the same $W_1$, $W_2$ find $W_1 + W_2$
and $\\dim(W_1 + W_2)$.

`Submodule.mem_sup_left` / `Submodule.mem_sup_right` put an element of $W_1$ / $W_2$ into
$W_1 + W_2$, and `sup_le_iff` says $W_1 + W_2 \\le U$ iff $W_1 \\le U$ and $W_2 \\le U$.
"

namespace LinearAlgebraGame

/-- $W_1 + W_2$: a basis $b_1, \dots, b_k$, and its dimension $k$. -/
Statement : ∃ k : ℕ, ∃ b : Fin k → Matrix (Fin 2) (Fin 2) ℝ,
    IsBasisOf b (S6W₁ ⊔ S6W₂) ∧ Module.finrank ℝ ↥(S6W₁ ⊔ S6W₂) = k := by
  Hint "Which matrices are sums of one from each? Find a basis on paper and prove it with
  `have`, as in the last level."
  Hint (hidden := true) "`have hS : IsBasisOf ![!![(0 : ℝ), 1; 0, 0], !![0, 0; 1, 0], !![0, 0; 0, 1]] (S6W₁ ⊔ S6W₂) := by`"
  have hS : IsBasisOf ![!![(0 : ℝ), 1; 0, 0], !![0, 0; 1, 0], !![0, 0; 0, 1]]
      (S6W₁ ⊔ S6W₂) := by
    constructor
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h01 := congrFun (congrFun hg 0) 1
      have h10 := congrFun (congrFun hg 1) 0
      have h11 := congrFun (congrFun hg 1) 1
      simp [Fin.sum_univ_three] at h01 h10 h11
      fin_cases i <;> simp [h01, h10, h11]
    · apply le_antisymm
      · Hint "Each generator of your span lies in $W_1$ or in $W_2$."
        Hint (hidden := true) "The first generator lies in $W_2$, the other two in $W_1$."
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact Submodule.mem_sup_right ⟨by simp, by simp⟩
        · exact Submodule.mem_sup_left ⟨by simp, by simp⟩
        · exact Submodule.mem_sup_left ⟨by simp, by simp⟩
      · Hint "It suffices that $W_1$ and $W_2$ are both inside the span."
        Hint (hidden := true) "`rw [sup_le_iff]`"
        rw [sup_le_iff]
        constructor
        · intro A hA
          obtain ⟨h00, h01⟩ := hA
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨![0, A 1 0, A 1 1], ?_⟩
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, h00, h01]
        · intro A hA
          obtain ⟨h00, h11⟩ := hA
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨![A 0 1, A 1 0, 0], ?_⟩
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, h00, h11]
  Hint (hidden := true) "`exact ⟨3, _, hS, hS.finrank_eq⟩`"
  exact ⟨3, _, hS, hS.finrank_eq⟩

end LinearAlgebraGame

Conclusion "
$\\dim(W_1\\cap W_2) = 1$, $\\dim(W_1+W_2) = 3 = 2 + 2 - 1$. Part (c) says this is no accident.
"

NewTheorem Submodule.mem_sup_left Submodule.mem_sup_right sup_le_iff
