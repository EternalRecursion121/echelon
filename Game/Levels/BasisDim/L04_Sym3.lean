import Game.Levels.BasisDim.L03_Sym2

World "BasisDim"
Level 4
Title "Symmetric 3×3 matrices"

-- @sheet 3 Q8b
/-! @answer
A symmetric $3\times3$ matrix is determined by its 3 diagonal entries and the 3 entries
above the diagonal:
$A = \sum_i a_{ii}E_{ii} + a_{12}(E_{12}+E_{21}) + a_{13}(E_{13}+E_{31}) + a_{23}(E_{23}+E_{32})$.
So $\langle E_{11}, E_{22}, E_{33}, E_{12}+E_{21}, E_{13}+E_{31}, E_{23}+E_{32}\rangle$ spans;
it is independent because each of the six entries $(1,1),(2,2),(3,3),(1,2),(1,3),(2,3)$ is
nonzero in exactly one of the six matrices. Dimension 6 (in general $n(n+1)/2$).
-/
Introduction "
**Problem Sheet 3, Question 8(b).** Find a basis for the space of symmetric
$3 \\times 3$ matrices.

The same strategy as in (a), with six matrices. (`Fin.sum_univ_six` expands a sum over six
indices.)
"

namespace LinearAlgebraGame

open Matrix

/-- $\langle E_{11}, E_{22}, E_{33}, E_{12}+E_{21}, E_{13}+E_{31}, E_{23}+E_{32}\rangle$ is a
basis of the symmetric $3\times3$ matrices. -/
Statement : IsBasisOf ![!![(1 : ℝ), 0, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 0],
    !![0, 0, 1; 0, 0, 0; 1, 0, 0], !![0, 0, 0; 0, 0, 1; 0, 1, 0]] (symMat 3) := by
  Hint "Same plan as (a): independence by reading off six entries, then two inclusions."
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    Hint (hidden := true) "Read off entries $(0,0), (1,1), (2,2), (0,1), (0,2), (1,2)$ with
    `congrFun (congrFun {hg} r) s`, then `simp [Fin.sum_univ_six] at …`."
    have h00 := congrFun (congrFun hg 0) 0
    have h11 := congrFun (congrFun hg 1) 1
    have h22 := congrFun (congrFun hg 2) 2
    have h01 := congrFun (congrFun hg 0) 1
    have h02 := congrFun (congrFun hg 0) 2
    have h12 := congrFun (congrFun hg 1) 2
    simp [Fin.sum_univ_six] at h00 h11 h22 h01 h02 h12
    fin_cases i <;> simp [h00, h11, h22, h01, h02, h12]
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> (ext j k; fin_cases j <;> fin_cases k <;> simp)
    · intro A hA
      Hint "The coefficients are the three diagonal entries and the three entries above the
      diagonal. Symmetry tells you the entries below."
      have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
      have h20 : A 2 0 = A 0 2 := congrFun (congrFun hA 0) 2
      have h21 : A 2 1 = A 1 2 := congrFun (congrFun hA 1) 2
      rw [Submodule.mem_span_range_iff_exists_fun]
      Hint (hidden := true) "`refine ⟨![A 0 0, A 1 1, A 2 2, A 0 1, A 0 2, A 1 2], ?_⟩`"
      refine ⟨![A 0 0, A 1 1, A 2 2, A 0 1, A 0 2, A 1 2], ?_⟩
      ext j k
      fin_cases j <;> fin_cases k <;> simp [Fin.sum_univ_six, h10, h20, h21]

end LinearAlgebraGame

Conclusion "
Six basis matrices: the dimension of the symmetric $3\\times3$ matrices is 6, and in general
$n(n+1)/2$.
"

NewTheorem Fin.sum_univ_six
TheoremTab "Basis"
