import Game.Levels.ChangeOfBasis.L04_RepUnique

World "ChangeOfBasis"
Level 5
Title "Equivalent matrices have equal rank"

Introduction "
Two $m\\times n$ matrices are **matrix equivalent** (Hefferon Def Three.V.2.3) if
$\\hat H = PHQ$ for nonsingular $P$, $Q$: they represent the same map with respect to
different bases. `MatEquiv H H'` says exactly that.

Changing bases cannot change the dimension of the range, so equivalent matrices have equal
rank. In matrix language: multiplying by a nonsingular matrix on either side preserves
rank — Mathlib's `Matrix.rank_mul_eq_left_of_isUnit_det` and
`Matrix.rank_mul_eq_right_of_isUnit_det`.
"

namespace LinearAlgebraGame

/-- Matrix-equivalent matrices have the same rank. -/
Statement rank_eq_of_matEquiv {m n : ℕ} (H H' : Matrix (Fin m) (Fin n) ℝ)
    (h : MatEquiv H H') : H.rank = H'.rank := by
  Hint "Unpack `{h}` into $P$, $Q$ and the equation."
  Hint (hidden := true) "`obtain ⟨P, Q, hP, hQ, rfl⟩ := {h}`"
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  Hint (hidden := true) "`rw [Matrix.rank_mul_eq_left_of_isUnit_det Q _ hQ,
  Matrix.rank_mul_eq_right_of_isUnit_det P H hP]`"
  rw [Matrix.rank_mul_eq_left_of_isUnit_det Q _ hQ, Matrix.rank_mul_eq_right_of_isUnit_det P H hP]

end LinearAlgebraGame

Conclusion "
Rank is an invariant of matrix equivalence. The boss shows it is the *only* one.
"

NewDefinition LinearAlgebraGame.MatEquiv
NewTheorem Matrix.rank_mul_eq_left_of_isUnit_det Matrix.rank_mul_eq_right_of_isUnit_det
TheoremTab "Change of basis"
