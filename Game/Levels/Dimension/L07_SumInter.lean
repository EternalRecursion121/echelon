import Game.Levels.Dimension.L06_DirectUnion

World "Dimension"
Level 7
Title "A sum and an intersection"

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
**Problem Sheet 6, Question 1(a).** For these subspaces of $\\mathcal M_{2\\times 2}$ find
$W_1 \\cap W_2$, $\\dim(W_1 \\cap W_2)$, $W_1 + W_2$, and $\\dim(W_1 + W_2)$:
$$W_1 = \\left\\{\\begin{pmatrix}0&0\\\\c&d\\end{pmatrix}\\right\\}, \\qquad
W_2 = \\left\\{\\begin{pmatrix}0&b\\\\c&0\\end{pmatrix}\\right\\}.$$

In Lean `S6W₁` is described as *entries $(0,0)$ and $(0,1)$ are zero* and `S6W₂` as
*entries $(0,0)$ and $(1,1)$ are zero* (`mem_S6W₁`, `mem_S6W₂`); entries are numbered from 0.
You describe each answer by a basis, then read off the dimension with `IsBasisOf.finrank_eq`.
`Submodule.mem_sup_left` / `Submodule.mem_sup_right` put an element of $W_1$ / $W_2$ into
$W_1 + W_2$.
"

namespace LinearAlgebraGame

/-- $W_1\cap W_2$ has basis $\langle E_{21}\rangle$ (dim 1); $W_1 + W_2$ has basis
$\langle E_{12}, E_{21}, E_{22}\rangle$ (dim 3). -/
Statement : IsBasisOf ![!![(0 : ℝ), 0; 1, 0]] (S6W₁ ⊓ S6W₂) ∧
    Module.finrank ℝ ↥(S6W₁ ⊓ S6W₂) = 1 ∧
    IsBasisOf ![!![(0 : ℝ), 1; 0, 0], !![0, 0; 1, 0], !![0, 0; 0, 1]] (S6W₁ ⊔ S6W₂) ∧
    Module.finrank ℝ ↥(S6W₁ ⊔ S6W₂) = 3 := by
  Hint "Prove the two basis claims first; the dimensions follow."
  have hI : IsBasisOf ![!![(0 : ℝ), 0; 1, 0]] (S6W₁ ⊓ S6W₂) := by
    constructor
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      have := congrFun (congrFun hg 1) 0
      fin_cases i
      simp at this
      exact this
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
      · Hint "A matrix in both subspaces has three zero entries."
        intro A hA
        obtain ⟨⟨h00, h01⟩, ⟨-, h11⟩⟩ := hA
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨![A 1 0], ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h00, h01, h11]
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
      · Hint "The first generator lies in $W_2$, the other two in $W_1$."
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
  exact ⟨hI, hI.finrank_eq, hS, hS.finrank_eq⟩

end LinearAlgebraGame

Conclusion "
$\\dim(W_1\\cap W_2) = 1$, $\\dim(W_1+W_2) = 3 = 2 + 2 - 1$. Part (c) says this is no accident.
"

NewDefinition LinearAlgebraGame.S6W₁ LinearAlgebraGame.S6W₂
NewTheorem LinearAlgebraGame.mem_S6W₁ LinearAlgebraGame.mem_S6W₂ Submodule.mem_sup_left Submodule.mem_sup_right sup_le_iff
TheoremTab "Sums"
