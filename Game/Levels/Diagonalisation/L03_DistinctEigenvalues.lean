import Game.Levels.Diagonalisation.L02_EigenColumns

World "Diagonalisation"
Level 3
Title "Two distinct eigenvalues"

Introduction "
**Corollary Five.II.3.19.** An $n \\times n$ matrix with $n$ distinct eigenvalues is
diagonalisable: one eigenvector for each eigenvalue gives $n$ vectors, independent by
Theorem 3.18 (your boss level `linearIndependent_of_eigen`), hence a basis of eigenvectors.

**Prove the $2 \\times 2$ case.** Plan:
1. unpack the two eigenvalues into eigenvectors $\\vec v, \\vec w$;
2. they are independent — apply `linearIndependent_of_eigen` to the map
   `Matrix.toLin' A` ($\\vec x \\mapsto A\\vec x$; `Matrix.toLin'_apply` unfolds it);
3. the matrix $Q$ with columns $\\vec v, \\vec w$ is written `(Matrix.of ![v, w])ᵀ` (rows $\\vec v$,
   $\\vec w$, transposed). Independent columns make it nonsingular:
   `Matrix.linearIndependent_col_iff_isUnit`;
4. finish with `diagonalizable_of_mul_eq`, checking $AQ = Q\\,\\mathrm{diag}(a, b)$ entry by
   entry.
"

namespace LinearAlgebraGame

open Matrix in
/-- A $2\times2$ matrix with two distinct eigenvalues is diagonalisable. -/
Statement diagonalizable_of_two_eigenvalues (A : Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ)
    (ha : IsEigenvalue A a) (hb : IsEigenvalue A b) (hab : a ≠ b) : Diagonalizable A := by
  Hint "Eigenvectors for $a$ and $b$ are independent, so they are the columns of a nonsingular
  $Q$ with $AQ = Q\\,\\mathrm\{diag}(a, b)$."
  Hint (hidden := true) "`obtain ⟨v, hv0, hv⟩ := ha` and `obtain ⟨w, hw0, hw⟩ := hb`."
  obtain ⟨v, hv0, hv⟩ := ha
  obtain ⟨w, hw0, hw⟩ := hb
  Hint (hidden := true) "`have hind : LinearIndependent ℝ ![v, w] := linearIndependent_of_eigen (toLin' A) v w a b (by rw [toLin'_apply, hv]) (by rw [toLin'_apply, hw]) hv0 hw0 hab`."
  have hind : LinearIndependent ℝ ![v, w] :=
    linearIndependent_of_eigen (toLin' A) v w a b (by rw [toLin'_apply, hv])
      (by rw [toLin'_apply, hw]) hv0 hw0 hab
  Hint (hidden := true) "`have hQ : IsUnit (Matrix.of ![v, w])ᵀ`: `rw [← linearIndependent_col_iff_isUnit]`
  and `exact hind`."
  have hQ : IsUnit (Matrix.of ![v, w])ᵀ := by
    rw [← linearIndependent_col_iff_isUnit]
    exact hind
  Hint (hidden := true) "`apply diagonalizable_of_mul_eq A _ hQ ![a, b]`."
  apply diagonalizable_of_mul_eq A _ hQ ![a, b]
  Hint (hidden := true) "Get the coordinate equations of `hv` and `hw`: `have h0 := congrFun hv 0`
  (and `1`, and the same for `hw`), then `simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h1 h2 h3`.
  Finally `entrywise <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith`."
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hw 0
  have h3 := congrFun hw 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at h0 h1 h2 h3
  entrywise <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

end LinearAlgebraGame

Conclusion "
With induction (Theorem 3.18 for $n$ vectors) the same proof gives Corollary 3.19 for every
$n$. The converse fails: $I$ is diagonal with only one eigenvalue. And with a repeated
eigenvalue anything can happen — compare $I$ with $\\begin{pmatrix}1&1\\\\0&1\\end{pmatrix}$.
"

NewTheorem LinearAlgebraGame.diagonalizable_of_mul_eq LinearAlgebraGame.linearIndependent_of_eigen Matrix.toLin'_apply Matrix.linearIndependent_col_iff_isUnit
TheoremTab "Eigen"
