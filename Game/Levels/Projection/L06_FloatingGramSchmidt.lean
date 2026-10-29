import Game.Levels.Projection.L05_GramSchmidtStep

World "Projection"
Level 6
Title "Gram–Schmidt in floating point"

-- @sheet 8 Q6a
/-! @answer
With $\kappa_1 = \beta_1 = (1,\varepsilon,0,0)$ we get $\kappa_1\cdot\kappa_1 = 1 + \varepsilon^2$, which
floating point rounds to $1$; the other dot products are computed exactly
($\beta_2\cdot\kappa_1 = \beta_3\cdot\kappa_1 = 1$). Then
$\kappa_2 = \beta_2 - \frac{\beta_2\cdot\kappa_1}{\kappa_1\cdot\kappa_1}\kappa_1 = \beta_2 - \kappa_1 = (0,-\varepsilon,\varepsilon,0)$
and, since $\beta_3\cdot\kappa_2 = 0$, $\kappa_3 = \beta_3 - \kappa_1 = (0,-\varepsilon,0,\varepsilon)$.
(The exact answers would be nearly orthogonal; these are not — see the next level.)
-/
Introduction "
**Problem Sheet 8, Question 6.** Let
$$\\vec\\beta_1 = (1, \\varepsilon, 0, 0),\\quad \\vec\\beta_2 = (1, 0, \\varepsilon, 0),\\quad
\\vec\\beta_3 = (1, 0, 0, \\varepsilon)$$
where $\\varepsilon > 0$ should be thought of as a small number. Assume that floating-point
arithmetic gives $1 + \\varepsilon^2 = 1$. Perform the Gram–Schmidt process using floating-point
arithmetic. Are the resulting vectors approximately orthogonal? Does scaling $\\vec\\kappa_2$ up help?

This level is the computation; the next one answers the two questions.

**A toy model of floating point.** Every dot product is passed through a rounding function
`fl : ℝ → ℝ`. You know only the sheet's rule: `fl (1 + ε^2) = 1`, and every other number is
represented exactly (`hex`). Part of your job is to work out **which** of the computed
quantities actually get rounded. The statement gives the vectors the computation produces;
check them.
"

namespace LinearAlgebraGame

open Matrix in
/-- Floating-point Gram–Schmidt (with the rule $\mathrm{fl}(1+\varepsilon^2) = 1$) produces
$\vec\kappa_2 = (0,-\varepsilon,\varepsilon,0)$ and $\vec\kappa_3 = (0,-\varepsilon,0,\varepsilon)$. -/
Statement (ε : ℝ) (hε : 0 < ε) (fl : ℝ → ℝ) (hfl : fl (1 + ε ^ 2) = 1)
    (hex : ∀ x, x ≠ 1 + ε ^ 2 → fl x = x) :
    let β₁ : Fin 4 → ℝ := ![1, ε, 0, 0]
    let β₂ : Fin 4 → ℝ := ![1, 0, ε, 0]
    let β₃ : Fin 4 → ℝ := ![1, 0, 0, ε]
    let κ₁ := β₁
    let κ₂ := β₂ - (fl (β₂ ⬝ᵥ κ₁) / fl (κ₁ ⬝ᵥ κ₁)) • κ₁
    let κ₃ := β₃ - (fl (β₃ ⬝ᵥ κ₁) / fl (κ₁ ⬝ᵥ κ₁)) • κ₁ - (fl (β₃ ⬝ᵥ κ₂) / fl (κ₂ ⬝ᵥ κ₂)) • κ₂
    κ₂ = ![0, -ε, ε, 0] ∧ κ₃ = ![0, -ε, 0, ε] := by
  Hint "Compute the dot products the algorithm feeds to `fl`, one at a time, and decide for
  each whether it is $1 + \\varepsilon^2$ (rounded) or something else (exact)."
  have hε2 : 0 < ε ^ 2 := by positivity
  Hint (hidden := true) "`have d11 : κ₁ ⬝ᵥ κ₁ = 1 + ε ^ 2 := by
  simp [κ₁, β₁, dotProduct, Fin.sum_univ_four]; ring`, and similarly `β₂ ⬝ᵥ κ₁ = 1`."
  have d11 : κ₁ ⬝ᵥ κ₁ = 1 + ε ^ 2 := by
    simp [κ₁, β₁, dotProduct, Fin.sum_univ_four]
    ring
  have d21 : β₂ ⬝ᵥ κ₁ = 1 := by simp [κ₁, β₁, β₂, dotProduct, Fin.sum_univ_four]
  have d31 : β₃ ⬝ᵥ κ₁ = 1 := by simp [κ₁, β₁, β₃, dotProduct, Fin.sum_univ_four]
  Hint (hidden := true) "Now apply the rounding rules: `have f11 : fl (κ₁ ⬝ᵥ κ₁) = 1 := by
  rw [d11, {hfl}]` and `have f21 : fl (β₂ ⬝ᵥ κ₁) = 1 := by rw [d21, {hex} 1 (by linarith)]`."
  have f11 : fl (κ₁ ⬝ᵥ κ₁) = 1 := by rw [d11, hfl]
  have f21 : fl (β₂ ⬝ᵥ κ₁) = 1 := by rw [d21, hex 1 (by linarith)]
  have f31 : fl (β₃ ⬝ᵥ κ₁) = 1 := by rw [d31, hex 1 (by linarith)]
  Hint "Now you can compute $\\vec\\kappa_2$ explicitly."
  have hκ₂ : κ₂ = ![0, -ε, ε, 0] := by
    simp only [κ₂, f21, f11, div_one, one_smul]
    entrywise <;> simp [κ₁, β₁, β₂]
  Hint (hidden := true) "For $\\vec\\kappa_3$ you also need `fl (β₃ ⬝ᵥ κ₂)`: compute
  `β₃ ⬝ᵥ κ₂` using `{hκ₂}` first."
  have f32 : fl (β₃ ⬝ᵥ κ₂) = 0 := by
    have d32 : β₃ ⬝ᵥ κ₂ = 0 := by
      rw [hκ₂]
      simp [β₃, dotProduct, Fin.sum_univ_four]
    rw [d32, hex 0 (by linarith)]
  refine ⟨hκ₂, ?_⟩
  simp only [κ₃, f31, f11, f32, div_one, one_smul, zero_div, zero_smul, sub_zero]
  entrywise <;> simp [κ₁, β₁, β₃]

end LinearAlgebraGame

Conclusion "
Only $\\vec\\kappa_1\\cdot\\vec\\kappa_1 = 1 + \\varepsilon^2$ was rounded — and that one rounding
turned $\\vec\\kappa_2$ and $\\vec\\kappa_3$ into $(0,-\\varepsilon,\\varepsilon,0)$ and
$(0,-\\varepsilon,0,\\varepsilon)$. Are they orthogonal? Next level.
"

TheoremTab "Projection"
NewTheorem div_one zero_div sub_zero
