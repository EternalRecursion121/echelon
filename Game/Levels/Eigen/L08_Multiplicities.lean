import Game.Levels.Eigen.L07_Eigenspaces

World "Eigen"
Level 8
Title "Multiplicities"

-- @sheet 9 Q7c
/-! @answer
The *algebraic multiplicity* of $\lambda$ is its multiplicity as a root of $|T - xI| = (x-1)(x-2)$:
$1$ for each of $\lambda = 1, 2$. The *geometric multiplicity* is $\dim V_\lambda$:
both eigenspaces are lines, so $1$ for each.
-/
Introduction "
**Problem Sheet 9, Question 7** (part 3 of 3). State the algebraic and geometric
multiplicities of the eigenvalues of $T = \\begin{pmatrix} 3 & 2 \\\\ -1 & 0\\end{pmatrix}$.

Algebraic multiplicity: `Polynomial.rootMultiplicity λ (charpolyH T)`.
Geometric multiplicity: `Module.finrank ℝ (eigenspace … λ)`, the dimension of $V_\\lambda$.
Your two previous results are in the inventory as `sheet9_q7a` and `sheet9_q7b`.
"

namespace LinearAlgebraGame

open Polynomial in
/-- Both eigenvalues $1$ and $2$ have algebraic multiplicity $1$ and geometric multiplicity $1$. -/
Statement :
    rootMultiplicity 1 (charpolyH (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) = 1 ∧
    rootMultiplicity 2 (charpolyH (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) = 1 ∧
    Module.finrank ℝ (Module.End.eigenspace
      (Matrix.toLin' (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) 1) = 1 ∧
    Module.finrank ℝ (Module.End.eigenspace
      (Matrix.toLin' (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) 2) = 1 := by
  Hint "Rewrite with what you already know, then: a simple root has multiplicity one, and
  the span of one nonzero vector has dimension one."
  Hint (hidden := true) "`rw [sheet9_q7a.1, sheet9_q7b.1, sheet9_q7b.2]`."
  rw [sheet9_q7a.1, sheet9_q7b.1, sheet9_q7b.2]
  have hne : (X - C 1) * (X - C 2) ≠ (0 : ℝ[X]) := mul_ne_zero (X_sub_C_ne_zero 1) (X_sub_C_ne_zero 2)
  Hint (hidden := true) "`rootMultiplicity_mul hne` splits the product;
  `rootMultiplicity_X_sub_C_self` and `rootMultiplicity_X_sub_C` evaluate the pieces."
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_self, rootMultiplicity_X_sub_C]
    norm_num
  · rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_self, rootMultiplicity_X_sub_C]
    norm_num
  · Hint (hidden := true) "`apply finrank_span_singleton`, then show the vector is not zero
    by looking at its first entry: `intro h; have := congrFun h 0; simp at this`."
    apply finrank_span_singleton
    intro h
    have := congrFun h 0
    simp at this
  · apply finrank_span_singleton
    intro h
    have := congrFun h 0
    simp at this

end LinearAlgebraGame

Conclusion "All multiplicities are $1$; with two distinct eigenvalues, $T$ is diagonalisable."

NewTheorem LinearAlgebraGame.sheet9_q7a LinearAlgebraGame.sheet9_q7b Polynomial.rootMultiplicity_mul Polynomial.rootMultiplicity_X_sub_C_self Polynomial.rootMultiplicity_X_sub_C Polynomial.X_sub_C_ne_zero finrank_span_singleton mul_ne_zero
NewDefinition Polynomial.rootMultiplicity
TheoremTab "Eigen"
