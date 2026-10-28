import Game.Levels.MatrixAlgebra.L08_SymmetricInverse

World "MatrixAlgebra"
Level 9
Title "Row sums of the inverse"

-- @sheet 8 Q4
/-! @answer
Let $\mathbb 1$ be the all-ones column. "Every row of $A$ sums to $k$" says $A\mathbb 1 = k\mathbb 1$.
Then $\mathbb 1 = A^{-1}A\mathbb 1 = A^{-1}(k\mathbb 1) = k\,A^{-1}\mathbb 1$. In particular $k \ne 0$
(otherwise $\mathbb 1 = 0$), and $A^{-1}\mathbb 1 = \tfrac1k\mathbb 1$, which says every row of
$A^{-1}$ sums to $1/k$.
-/
Introduction "
**Problem Sheet 8, Question 4.** Let $A$ be a nonsingular matrix. Prove: if the sum of the
elements of each row of $A$ is $k$, then the sum of the elements in each row of $A^{-1}$ is
$1/k$.

The all-ones vector is `fun _ => 1`. Row $i$ of $A$ summing to $k$ is the $i$-th entry of
$A\\mathbb 1 = k\\mathbb 1$.
"

namespace LinearAlgebraGame

open Matrix in
/-- If every row of the nonsingular $A$ sums to $k$, every row of $A^{-1}$ sums to $1/k$. -/
Statement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (k : ℝ)
    (h : ∀ i, ∑ j, A i j = k) : ∀ i, ∑ j, A⁻¹ i j = 1 / k := by
  intro i
  Hint "Restate the hypothesis as $A\\mathbb 1 = k\\mathbb 1$."
  Hint (hidden := true) "`have hA1 : A *ᵥ (fun _ => 1) = k • (fun _ => 1)`, by `ext l` and
  `simp [Matrix.mulVec, dotProduct, h]`."
  have hA1 : A *ᵥ (fun _ => 1) = k • (fun _ => 1) := by
    ext l
    simp [Matrix.mulVec, dotProduct, h]
  Hint "Now apply $A^\{-1}$ to both sides."
  Hint (hidden := true) "`have key : A⁻¹ *ᵥ (A *ᵥ (fun _ => 1)) = fun _ => 1`, by
  `rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]`."
  have key : A⁻¹ *ᵥ (A *ᵥ (fun _ => 1)) = fun _ => 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
  rw [hA1, Matrix.mulVec_smul] at key
  Hint (hidden := true) "Take entry `i`: `have hi := congrFun key i` and
  `simp [Matrix.mulVec, dotProduct] at hi`."
  have hi := congrFun key i
  simp [Matrix.mulVec, dotProduct] at hi
  Hint "Why can $k$ not be $0$?"
  have hk : k ≠ 0 := by
    intro hk0
    rw [hk0, zero_mul] at hi
    norm_num at hi
  field_simp
  linarith

end LinearAlgebraGame

Conclusion "
The all-ones vector is an eigenvector of $A$ with eigenvalue $k$, hence of $A^{-1}$ with
eigenvalue $1/k$ — a preview of Chapter Five.
"

TheoremTab "Matrices"
