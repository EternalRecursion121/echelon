import Game.Metadata
import Game.Ch45
import Game.Levels.Eigen

World "Diagonalisation"
Level 1
Title "A matrix that cannot be diagonalised"

Introduction "
**Definition Five.II.2.1.** $T$ is *diagonalisable* if it is similar to a diagonal matrix.
In Lean: `Diagonalizable T` means `∃ d, MatSimilar T (Matrix.diagonal d)`.

Hefferon's non-example is $N = \\begin{pmatrix} 0 & 0 \\\\ 1 & 0 \\end{pmatrix}$: $N \\ne 0$ but $N^2 = 0$.
If $D = PNP^{-1}$ were diagonal, then $D^2 = PN^2P^{-1} = 0$, so every diagonal entry
satisfies $d_i^2 = 0$, so $D = 0$ and $N = P^{-1}DP = 0$ — contradiction.

**Prove it for every** nonzero $N$ with $N^2 = 0$.
"

namespace LinearAlgebraGame

open Matrix in
/-- A nonzero matrix $N$ with $N^2 = 0$ is not diagonalisable. -/
Statement not_diagonalizable_of_sq_eq_zero {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (h2 : N * N = 0) (h0 : N ≠ 0) : ¬ Diagonalizable N := by
  Hint "Suppose diag(d) = P N P⁻¹. Show diag(d)² = 0, deduce diag(d) = 0, then N = 0."
  intro h
  obtain ⟨d, P, hP, hD⟩ := h
  Hint (hidden := true) "`have hDD : diagonal d * diagonal d = 0`: rewrite with `hD`, regroup with
  `calc`, and cancel `P⁻¹ * P`."
  have hDD : diagonal d * diagonal d = 0 := by
    rw [hD]
    calc P * N * P⁻¹ * (P * N * P⁻¹) = P * N * (P⁻¹ * P) * N * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [inv_mul_of_isUnit hP, Matrix.mul_one, Matrix.mul_assoc P, h2, Matrix.mul_zero,
            Matrix.zero_mul]
  Hint (hidden := true) "`have hd : diagonal d = 0`. Use `diagonal_mul_diagonal`,
  `← diagonal_zero` and `diagonal_eq_diagonal_iff` to reduce to `d i * d i = 0`, then `mul_self_eq_zero`."
  have hd : diagonal d = 0 := by
    rw [diagonal_mul_diagonal, ← diagonal_zero, diagonal_eq_diagonal_iff] at hDD
    rw [← diagonal_zero, diagonal_eq_diagonal_iff]
    intro i
    exact mul_self_eq_zero.1 (hDD i)
  apply h0
  Hint (hidden := true) "`calc N = P⁻¹ * (P * N * P⁻¹) * P := …`, then `_ = 0` using `← hD` and `hd`."
  calc N = P⁻¹ * (P * N * P⁻¹) * P := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, inv_mul_of_isUnit hP, Matrix.mul_one,
          ← Matrix.mul_assoc, inv_mul_of_isUnit hP, Matrix.one_mul]
    _ = 0 := by rw [← hD, hd, Matrix.mul_zero, Matrix.zero_mul]

end LinearAlgebraGame

Conclusion "
*Nilpotent* matrices other than $0$ are never diagonalisable. Equivalently (Lemma 2.4),
$N$ has no basis of eigenvectors: its only eigenvalue is $0$ and its eigenspace is a line.
"

NewDefinition LinearAlgebraGame.Diagonalizable
NewTheorem Matrix.diagonal_zero Matrix.diagonal_eq_diagonal_iff mul_self_eq_zero Polynomial.coeff_natDegree
TheoremTab "Eigen"
