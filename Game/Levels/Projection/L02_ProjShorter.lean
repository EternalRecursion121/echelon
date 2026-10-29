import Game.Levels.Projection.L01_ProjectOntoLine

World "Projection"
Level 2
Title "A projection is no longer than the vector"

-- @sheet 7 Q9
/-! @answer
Let $\vec p = \mathrm{proj}_{[\vec s]}(\vec v)$. Then $\vec v = \vec p + (\vec v - \vec p)$, and
$\vec p\cdot(\vec v - \vec p) = 0$ since $\vec p$ is a multiple of $\vec s$ and $\vec v - \vec p \perp \vec s$.
Expanding (Pythagoras), $|\vec v|^2 = |\vec p|^2 + |\vec v - \vec p|^2 \ge |\vec p|^2$, and taking
square roots, $|\vec p| \le |\vec v|$.
-/
Introduction "
**Problem Sheet 7, Question 9.** Prove that the orthogonal projection of a vector into a line
has length less than or equal to that of the vector.

Length is $|\\vec v| = \\sqrt{\\vec v\\cdot\\vec v}$; `Real.sqrt_le_sqrt` reduces the claim to the
squared lengths. You will also want `dot_self_nonneg : 0 ≤ v ⬝ᵥ v`.
"

namespace LinearAlgebraGame

open Matrix in
/-- $|\mathrm{proj}_{[\vec s]}(\vec v)| \le |\vec v|$. -/
Statement {n : ℕ} (s v : Fin n → ℝ) (hs : s ≠ 0) :
    Real.sqrt (projLine s v ⬝ᵥ projLine s v) ≤ Real.sqrt (v ⬝ᵥ v) := by
  Hint "Pythagoras: $\\vec v = \\vec p + (\\vec v - \\vec p)$ with the two parts orthogonal."
  apply Real.sqrt_le_sqrt
  Hint "First record that $\\vec v - \\vec p$ is orthogonal to $\\vec p$ (not just to $\\vec s$)."
  Hint "Careful when you unfold: `rw [projLine]` unfolds *every* copy of
  `projLine s v`, including the one inside `v - projLine s v`, and then `projLine_orth` no
  longer matches. `nth_rw 2 [projLine]` unfolds only the second copy."
  Hint (hidden := true) "`have horth : (v - projLine s v) ⬝ᵥ projLine s v = 0`, proved by
  `nth_rw 2 [projLine]` and `rw [dotProduct_smul, projLine_orth s v {hs}, smul_zero]`."
  have horth : (v - projLine s v) ⬝ᵥ projLine s v = 0 := by
    nth_rw 2 [projLine]
    rw [dotProduct_smul, projLine_orth s v hs, smul_zero]
  Hint "Now expand $\\vec v\\cdot\\vec v$."
  Hint (hidden := true) "`have hv : v ⬝ᵥ v = projLine s v ⬝ᵥ projLine s v +
  (v - projLine s v) ⬝ᵥ (v - projLine s v)`: write `v` as `projLine s v + (v - projLine s v)`
  (`add_sub_cancel`) and expand with `add_dotProduct`, `dotProduct_add`, `dotProduct_comm`."
  have hv : v ⬝ᵥ v = projLine s v ⬝ᵥ projLine s v +
      (v - projLine s v) ⬝ᵥ (v - projLine s v) := by
    calc v ⬝ᵥ v = (projLine s v + (v - projLine s v)) ⬝ᵥ (projLine s v + (v - projLine s v)) := by
          rw [add_sub_cancel]
      _ = _ := by
          rw [add_dotProduct, dotProduct_add, dotProduct_add,
            dotProduct_comm (projLine s v) (v - projLine s v), horth]
          ring
  have := dot_self_nonneg (v - projLine s v)
  linarith

end LinearAlgebraGame

Conclusion "
$|\\vec v|^2 = |\\mathrm{proj}|^2 + |\\vec v - \\mathrm{proj}|^2$: the projection is the leg of a right
triangle whose hypotenuse is $\\vec v$.
"

NewTheorem Real.sqrt_le_sqrt add_sub_cancel
TheoremTab "Projection"
