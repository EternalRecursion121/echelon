import Game.Levels.Determinant.L01_EqualRows

World "Determinant"
Level 2
Title "A zero row"

Introduction "
**Lemma Four.I.2.4 (2).** If some row of $M$ is zero, then $d(M) = 0$.

Lean's `M.updateRow i r` is $M$ with row $i$ replaced by $r$; condition (3) is
`hd.scale M i k : d (M.updateRow i (k • M i)) = k * d M`.
"

namespace LinearAlgebraGame

/-- If row $i$ of $M$ is zero, then $d(M) = 0$ for every determinant function $d$. -/
Statement det_eq_zero_of_row_zero {n : ℕ} (d : Matrix (Fin n) (Fin n) ℝ → ℝ) (hd : DetAxioms d)
    (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (h : M i = 0) : d M = 0 := by
  Hint "Idea: multiplying the zero row by $0$ does not change the matrix, but condition (3)
  says it multiplies $d(M)$ by $0$."
  Hint (hidden := true) "`have h1 := hd.scale {M} {i} 0`."
  have h1 := hd.scale M i 0
  Hint (hidden := true) "Rewrite `{h1}` with `zero_smul`, then `← {h}` (turning the zero row
  back into `M i`), then `updateRow_eq_self` and `zero_mul`."
  rw [zero_smul, ← h, Matrix.updateRow_eq_self, zero_mul] at h1
  exact h1

end LinearAlgebraGame

Conclusion "Hefferon's proof is the same: scale the zero row."

NewTheorem Matrix.updateRow_eq_self
TheoremTab "Det"
