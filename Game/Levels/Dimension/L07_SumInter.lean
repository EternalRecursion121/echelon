import Game.Levels.Dimension.L06_DirectUnion

World "Dimension"
Level 7
Title "An intersection"

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
This level: $W_1 \\cap W_2$; the next level: $W_1 + W_2$.
You describe each answer by a basis, then read off the dimension with `IsBasisOf.finrank_eq`.
`Submodule.mem_sup_left` / `Submodule.mem_sup_right` put an element of $W_1$ / $W_2$ into
$W_1 + W_2$.
"

namespace LinearAlgebraGame

/-- $W_1 \cap W_2$: a basis $b_1, \dots, b_k$, and its dimension $k$. -/
Statement : ∃ k : ℕ, ∃ b : Fin k → Matrix (Fin 2) (Fin 2) ℝ,
    IsBasisOf b (S6W₁ ⊓ S6W₂) ∧ Module.finrank ℝ ↥(S6W₁ ⊓ S6W₂) = k := by
  Hint "Which matrices lie in both? Find a basis on paper. In Lean, prove the basis claim with
  `have`; the dimension then follows from `IsBasisOf.finrank_eq`."
  Hint (hidden := true) "`have hI : IsBasisOf ![!![(0 : ℝ), 0; 1, 0]] (S6W₁ ⊓ S6W₂) := by`"
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
  Hint (hidden := true) "`exact ⟨1, _, hI, hI.finrank_eq⟩`"
  exact ⟨1, _, hI, hI.finrank_eq⟩

end LinearAlgebraGame

Conclusion "$W_1 \\cap W_2 = \\{\\begin{pmatrix}0&0\\\\c&0\\end{pmatrix}\\}$, dimension $1$."

NewDefinition LinearAlgebraGame.S6W₁ LinearAlgebraGame.S6W₂
NewTheorem LinearAlgebraGame.mem_S6W₁ LinearAlgebraGame.mem_S6W₂
TheoremTab "Sums"
