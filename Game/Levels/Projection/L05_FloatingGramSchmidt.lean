import Game.Levels.Projection.L04_GramSchmidtStep

World "Projection"
Level 5
Title "Gram–Schmidt in floating point"

-- @sheet 8 Q6
/-! @answer
With $\kappa_1 = \beta_1 = (1,\varepsilon,0,0)$ we get $\kappa_1\cdot\kappa_1 = 1 + \varepsilon^2$, which
floating point rounds to $1$; the other dot products are computed exactly. Then
$\kappa_2 = \beta_2 - \frac{\beta_2\cdot\kappa_1}{\kappa_1\cdot\kappa_1}\kappa_1 = \beta_2 - \kappa_1 = (0,-\varepsilon,\varepsilon,0)$
and, since $\beta_3\cdot\kappa_2 = 0$, $\kappa_3 = \beta_3 - \kappa_1 = (0,-\varepsilon,0,\varepsilon)$.
Now $\kappa_2\cdot\kappa_3 = \varepsilon^2$ and $|\kappa_2| = |\kappa_3| = \sqrt2\,\varepsilon$, so
$\cos\angle(\kappa_2,\kappa_3) = \varepsilon^2/(2\varepsilon^2) = 1/2$: the angle is $60^\circ$.
**The computed vectors are far from orthogonal.** **Scaling $\kappa_2$ up does not help**: the
cosine of an angle is unchanged when a vector is multiplied by $c > 0$ (and the projection of
$\beta_3$ onto $c\kappa_2$ is the same as onto $\kappa_2$). The trouble is that the rounding error
in $\kappa_1\cdot\kappa_1$ is of the same size, $\varepsilon^2$, as the quantities that should cancel.
(Modified Gram–Schmidt, which subtracts each projection from the running vector, behaves better:
it computes $\kappa_3$ using $\beta_3 - \kappa_1$ against $\kappa_2$, giving a nonzero correction.)
-/
Introduction "
**Problem Sheet 8, Question 6.** Let
$$\\vec\\beta_1 = (1, \\varepsilon, 0, 0),\\quad \\vec\\beta_2 = (1, 0, \\varepsilon, 0),\\quad
\\vec\\beta_3 = (1, 0, 0, \\varepsilon)$$
where $\\varepsilon > 0$ should be thought of as a small number. Assume that floating-point
arithmetic gives $1 + \\varepsilon^2 = 1$. Perform the Gram–Schmidt process using floating-point
arithmetic. Are the resulting vectors approximately orthogonal? Does scaling $\\vec\\kappa_2$ up help?

**A toy model of floating point.** Every dot product is passed through a rounding function
`fl : ℝ → ℝ`. You know only the sheet's rule: `fl (1 + ε^2) = 1`, and every other number is
represented exactly (`hex`). Part of your job is to work out **which** of the computed
quantities actually get rounded. The statement asks for the cosine of the angle between the
computed $\\vec\\kappa_2, \\vec\\kappa_3$ (an angle of $\\theta$ has $\\cos\\theta = \\vec u\\cdot\\vec w/|\\vec u||\\vec w|$),
and then the same cosine after scaling $\\vec\\kappa_2$ by any $c > 0$.

This is an **explain level**: also write your answer to the two questions as a comment block
starting `-- Explain:` inside your proof.
"

namespace LinearAlgebraGame

open Matrix in
/-- Floating-point Gram–Schmidt (with the rule $\mathrm{fl}(1+\varepsilon^2) = 1$) produces
$\vec\kappa_2, \vec\kappa_3$ with $\cos\angle = 1/2$, and scaling $\vec\kappa_2$ by $c > 0$ keeps it $1/2$. -/
Statement (ε : ℝ) (hε : 0 < ε) (fl : ℝ → ℝ) (hfl : fl (1 + ε ^ 2) = 1)
    (hex : ∀ x, x ≠ 1 + ε ^ 2 → fl x = x) :
    let β₁ : Fin 4 → ℝ := ![1, ε, 0, 0]
    let β₂ : Fin 4 → ℝ := ![1, 0, ε, 0]
    let β₃ : Fin 4 → ℝ := ![1, 0, 0, ε]
    let κ₁ := β₁
    let κ₂ := β₂ - (fl (β₂ ⬝ᵥ κ₁) / fl (κ₁ ⬝ᵥ κ₁)) • κ₁
    let κ₃ := β₃ - (fl (β₃ ⬝ᵥ κ₁) / fl (κ₁ ⬝ᵥ κ₁)) • κ₁ - (fl (β₃ ⬝ᵥ κ₂) / fl (κ₂ ⬝ᵥ κ₂)) • κ₂
    κ₂ ⬝ᵥ κ₃ / Real.sqrt ((κ₂ ⬝ᵥ κ₂) * (κ₃ ⬝ᵥ κ₃)) = 1 / 2 ∧
    ∀ c : ℝ, 0 < c →
      (c • κ₂) ⬝ᵥ κ₃ / Real.sqrt (((c • κ₂) ⬝ᵥ (c • κ₂)) * (κ₃ ⬝ᵥ κ₃)) = 1 / 2 := by
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
    ext i
    fin_cases i <;> simp [κ₁, β₁, β₂]
  have d32 : β₃ ⬝ᵥ κ₂ = 0 := by
    rw [hκ₂]
    simp [β₃, dotProduct, Fin.sum_univ_four]
  have d22 : κ₂ ⬝ᵥ κ₂ = 2 * ε ^ 2 := by
    rw [hκ₂]
    simp [dotProduct, Fin.sum_univ_four]
    ring
  have f32 : fl (β₃ ⬝ᵥ κ₂) = 0 := by rw [d32, hex 0 (by linarith)]
  have hκ₃ : κ₃ = ![0, -ε, 0, ε] := by
    simp only [κ₃, f31, f11, f32, div_one, one_smul, zero_div, zero_smul, sub_zero]
    ext i
    fin_cases i <;> simp [κ₁, β₁, β₃]
  have d23 : κ₂ ⬝ᵥ κ₃ = ε ^ 2 := by
    rw [hκ₂, hκ₃]
    simp [dotProduct, Fin.sum_univ_four]
    ring
  have d33 : κ₃ ⬝ᵥ κ₃ = 2 * ε ^ 2 := by
    rw [hκ₃]
    simp [dotProduct, Fin.sum_univ_four]
    ring
  Hint (hidden := true) "`Real.sqrt_mul_self` : `0 ≤ a → √(a * a) = a`."
  have hsq : Real.sqrt ((2 * ε ^ 2) * (2 * ε ^ 2)) = 2 * ε ^ 2 :=
    Real.sqrt_mul_self (by positivity)
  constructor
  · rw [d23, d22, d33, hsq]
    field_simp
  · intro c hc
    rw [smul_dotProduct, smul_dotProduct, dotProduct_smul, d23, d22, d33, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    have hcs : c * (c * (2 * ε ^ 2)) * (2 * ε ^ 2) = (c * (2 * ε ^ 2)) * (c * (2 * ε ^ 2)) := by
      ring
    rw [hcs, Real.sqrt_mul_self (by positivity)]
    Hint (hidden := true) "Model explanation: only $\\kappa_1\\cdot\\kappa_1 = 1+\\varepsilon^2$ is
    rounded. The computed $\\kappa_2 = (0,-\\varepsilon,\\varepsilon,0)$ and $\\kappa_3 = (0,-\\varepsilon,0,\\varepsilon)$
    meet at $60^\\circ$ ($\\cos = 1/2$), so they are far from orthogonal. Scaling $\\kappa_2$ by
    $c > 0$ changes neither $\\kappa_3$ nor any angle, so it does not help: the rounding error in
    $\\kappa_1\\cdot\\kappa_1$ is as large as the $\\varepsilon^2$-sized quantities that should cancel."
    -- Explain: …
    field_simp

end LinearAlgebraGame

Conclusion "
The computed vectors meet at $60^\\circ$, not $90^\\circ$, and rescaling cannot fix an angle.
Rounding $1+\\varepsilon^2$ to $1$ is an error of size $\\varepsilon^2$ — exactly the size of the
quantities that were supposed to cancel. (Chapter Six returns to stable variants such as
modified Gram–Schmidt.)
"

TheoremTab "Projection"
NewTheorem div_one zero_div Real.sqrt_mul_self sub_zero
