import Game.Levels.BasisDim.L02_P2Basis

World "BasisDim"
Level 3
Title "Symmetric 2×2 matrices"

-- @sheet 3 Q8a
/-! @answer
A symmetric $2\times 2$ matrix has the form $\begin{pmatrix} a & b\\ b & d\end{pmatrix}
= a\begin{pmatrix}1&0\\0&0\end{pmatrix} + d\begin{pmatrix}0&0\\0&1\end{pmatrix}
+ b\begin{pmatrix}0&1\\1&0\end{pmatrix}$, so these three symmetric matrices span the space.
They are independent: if $aE_{11} + dE_{22} + b(E_{12}+E_{21}) = 0$ then reading off entries
$(1,1)$, $(2,2)$, $(1,2)$ gives $a = d = b = 0$. So
$\langle E_{11}, E_{22}, E_{12} + E_{21}\rangle$ is a basis (and the space has dimension 3).
-/
Introduction "
**Problem Sheet 3, Question 8.** A square matrix is symmetric if for all indices $i$ and
$j$, entry $i,j$ equals entry $j,i$.
**(a)** Find a basis for the vector space of symmetric $2 \\times 2$ matrices.

`symMat n` is the subspace of $n\\times n$ matrices with $A^T = A$
(`mem_symMat` unfolds membership). You supply a basis — a number $k$ and a
sequence `b : Fin k → Matrix (Fin 2) (Fin 2) ℝ` — and prove it is a basis: independent, and
its span is exactly `symMat 2`. Entries are numbered from `0`.
"

namespace LinearAlgebraGame

open Matrix

/-- The symmetric $2\times 2$ matrices have a basis $b_1, \dots, b_k$. -/
Statement : ∃ k : ℕ, ∃ b : Fin k → Matrix (Fin 2) (Fin 2) ℝ, IsBasisOf b (symMat 2) := by
  Hint "Find a basis on paper: how many free entries does a symmetric $2\\times 2$ matrix have?
  Then `use` the number of basis vectors and the basis (a vector `![…]` of matrices)."
  Hint (hidden := true) "`use 3, ![!![1, 0; 0, 0], !![0, 0; 0, 1], !![0, 1; 1, 0]]`"
  use 3, ![!![1, 0; 0, 0], !![0, 0; 0, 1], !![0, 1; 1, 0]]
  Hint "Two parts: independence, then the span is exactly the symmetric matrices."
  constructor
  · Hint "Independence: suppose $\\sum g_i E_i = 0$ and read off the entries $(0,0)$,
    $(1,1)$ and $(0,1)$."
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    Hint (hidden := true) "`have h00 := congrFun (congrFun {hg} 0) 0` reads off entry
    $(0,0)$. Do the same for $(1,1)$ and $(0,1)$, then `simp [Fin.sum_univ_three] at …`."
    have h00 := congrFun (congrFun hg 0) 0
    have h11 := congrFun (congrFun hg 1) 1
    have h01 := congrFun (congrFun hg 0) 1
    simp [Fin.sum_univ_three] at h00 h11 h01
    fin_cases i <;> simp [h00, h11, h01]
  · Hint "Show both inclusions."
    Hint (hidden := true) "`apply le_antisymm`"
    apply le_antisymm
    · Hint "The span is inside the symmetric matrices if each generator is symmetric."
      Hint (hidden := true) "`rw [Submodule.span_le]`"
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      Hint (hidden := true) "`fin_cases i <;> (ext j k; fin_cases j <;> fin_cases k <;> simp)`"
      fin_cases i <;> (ext j k; fin_cases j <;> fin_cases k <;> simp)
    · Hint "Conversely, write a symmetric $A$ as a combination: the coefficients are
      the entries at positions (0,0), (1,1) and (0,1)."
      intro A hA
      have hA' : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
      rw [Submodule.mem_span_range_iff_exists_fun]
      Hint (hidden := true) "`refine ⟨![A 0 0, A 1 1, A 0 1], ?_⟩`, then compare all entries."
      refine ⟨![A 0 0, A 1 1, A 0 1], ?_⟩
      ext j k
      fin_cases j <;> fin_cases k <;> simp [Fin.sum_univ_three, hA']

end LinearAlgebraGame

Conclusion "
A basis: $\\langle E_{11}, E_{22}, E_{12}+E_{21}\\rangle$ — so the space has dimension 3.
"

NewDefinition LinearAlgebraGame.symMat
NewTheorem LinearAlgebraGame.mem_symMat
TheoremTab "Basis"
