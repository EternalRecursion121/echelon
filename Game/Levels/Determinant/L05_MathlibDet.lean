import Game.Levels.Determinant.L04_Triangular

World "Determinant"
Level 5
Title "Existence"

Introduction "
Does a determinant function exist? Hefferon builds one from the permutation expansion
(Theorem Four.I.3.14). Mathlib *defines* `Matrix.det` as exactly that expansion,
$\\det T = \\sum_\\sigma \\operatorname{sgn}(\\sigma)\\, t_{\\sigma(1),1}\\cdots t_{\\sigma(n),n}$,
and proves the four conditions as theorems. Check that it qualifies.
"

namespace LinearAlgebraGame

/-- Mathlib's determinant satisfies Hefferon's four conditions. -/
Statement detAxioms_det {n : ℕ} : DetAxioms (fun M : Matrix (Fin n) (Fin n) ℝ => M.det) := by
  Hint "`constructor` splits the goal into the four conditions. Each is a theorem in your
  inventory."
  constructor
  · Hint (hidden := true) "`intro M i j h` then `exact det_swapRows M h`."
    intro M i j h
    exact det_swapRows M h
  · Hint (hidden := true) "`intro M i j k h` then `exact Matrix.det_updateRow_add_smul_self M h.symm k`."
    intro M i j k h
    exact Matrix.det_updateRow_add_smul_self M h.symm k
  · Hint (hidden := true) "`intro M i k`, then `rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]`."
    intro M i k
    rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  · exact Matrix.det_one

end LinearAlgebraGame

Conclusion "
Existence (this level) plus uniqueness (the last two levels) is Hefferon's Theorem
Four.I.3.14. From now on, every result about `DetAxioms` applies to `Matrix.det`.
"

NewTheorem LinearAlgebraGame.det_swapRows Matrix.det_updateRow_add_smul_self Matrix.det_updateRow_smul

TheoremTab "Det"
