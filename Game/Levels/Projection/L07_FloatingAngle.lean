import Game.Levels.Projection.L06_FloatingGramSchmidt

World "Projection"
Level 7
Title "How orthogonal is the computed basis?"

-- @sheet 8 Q6
/-! @answer
The computed vectors are $\kappa_2 = (0,-\varepsilon,\varepsilon,0)$ and
$\kappa_3 = (0,-\varepsilon,0,\varepsilon)$. Now $\kappa_2\cdot\kappa_3 = \varepsilon^2$ and
$|\kappa_2| = |\kappa_3| = \sqrt2\,\varepsilon$, so
$\cos\angle(\kappa_2,\kappa_3) = \varepsilon^2/(2\varepsilon^2) = 1/2$: the angle is $60^\circ$, whatever
$\varepsilon$ is. **The computed vectors are far from orthogonal.** **Scaling $\kappa_2$ up does not
help**: the cosine of an angle is unchanged when a vector is multiplied by $c > 0$ (and since
$\beta_3\cdot\kappa_2 = 0$, the projection of $\beta_3$ onto $c\kappa_2$ is zero too, so $\kappa_3$
does not change). The trouble is that the rounding error in $\kappa_1\cdot\kappa_1$ is of the same
size, $\varepsilon^2$, as the quantities that should cancel. (Modified Gram–Schmidt, which
subtracts each projection from the running vector, behaves better.)
-/
Introduction "
**Problem Sheet 8, Question 6, continued.** Floating-point Gram–Schmidt produced
$\\vec\\kappa_2 = (0,-\\varepsilon,\\varepsilon,0)$ and $\\vec\\kappa_3 = (0,-\\varepsilon,0,\\varepsilon)$.
Are they approximately orthogonal? Does scaling $\\vec\\kappa_2$ up help? (Scaling $\\vec\\kappa_2$
does not change $\\vec\\kappa_3$: you computed $\\vec\\beta_3\\cdot\\vec\\kappa_2 = 0$.)

The angle $\\theta$ between $\\vec u$ and $\\vec w$ has
$\\cos\\theta = \\vec u\\cdot\\vec w/(|\\vec u|\\,|\\vec w|)$. To avoid square roots we work with
$$\\cos^2\\theta = \\frac{(\\vec u\\cdot\\vec w)^2}{(\\vec u\\cdot\\vec u)(\\vec w\\cdot\\vec w)}$$
(orthogonal means $\\cos^2\\theta = 0$). **Find** the number $c = \\cos^2\\theta$: the same $c$ must
work for every $\\varepsilon > 0$ and after scaling $\\vec\\kappa_2$ by any $k > 0$.

This is an **explain level**: also write your answer to the two questions as a comment block
starting `-- Explain:` inside your proof.
"

namespace LinearAlgebraGame

open Matrix in
/-- There is one number $c \ge 1/4$ that is $\cos^2$ of the angle between the computed
$\vec\kappa_2, \vec\kappa_3$ for every $\varepsilon > 0$, and stays the same when $\vec\kappa_2$
is scaled by any $k > 0$. -/
Statement : ∃ c : ℝ, 1 / 4 ≤ c ∧ ∀ ε : ℝ, 0 < ε →
    let κ₂ : Fin 4 → ℝ := ![0, -ε, ε, 0]
    let κ₃ : Fin 4 → ℝ := ![0, -ε, 0, ε]
    (κ₂ ⬝ᵥ κ₃) ^ 2 / ((κ₂ ⬝ᵥ κ₂) * (κ₃ ⬝ᵥ κ₃)) = c ∧
    ∀ k : ℝ, 0 < k → ((k • κ₂) ⬝ᵥ κ₃) ^ 2 / (((k • κ₂) ⬝ᵥ (k • κ₂)) * (κ₃ ⬝ᵥ κ₃)) = c := by
  Hint "Compute $\\vec\\kappa_2\\cdot\\vec\\kappa_3$, $\\vec\\kappa_2\\cdot\\vec\\kappa_2$ and
  $\\vec\\kappa_3\\cdot\\vec\\kappa_3$ on paper. What is $\\cos^2\\theta$? Does $\\varepsilon$ survive?"
  Hint (hidden := true) "`use 1 / 4`, then `constructor`."
  use 1 / 4
  constructor
  · norm_num
  intro ε hε κ₂ κ₃
  Hint (hidden := true) "Record the three dot products, e.g. `have d23 : κ₂ ⬝ᵥ κ₃ = ε ^ 2 := by
  simp [κ₂, κ₃, dotProduct, Fin.sum_univ_four]; ring`."
  have d23 : κ₂ ⬝ᵥ κ₃ = ε ^ 2 := by
    simp [κ₂, κ₃, dotProduct, Fin.sum_univ_four]
    ring
  have d22 : κ₂ ⬝ᵥ κ₂ = 2 * ε ^ 2 := by
    simp [κ₂, dotProduct, Fin.sum_univ_four]
    ring
  have d33 : κ₃ ⬝ᵥ κ₃ = 2 * ε ^ 2 := by
    simp [κ₃, dotProduct, Fin.sum_univ_four]
    ring
  constructor
  · Hint (hidden := true) "`rw [d23, d22, d33]`, then `field_simp` and `ring`."
    rw [d23, d22, d33]
    field_simp
    ring
  · intro k hk
    Hint (hidden := true) "Pull $k$ out with `smul_dotProduct`, `dotProduct_smul` and
    `smul_eq_mul`, then as before."
    Hint (hidden := true) "Model explanation: only $\\kappa_1\\cdot\\kappa_1 = 1+\\varepsilon^2$ is
    rounded. The computed $\\kappa_2 = (0,-\\varepsilon,\\varepsilon,0)$ and $\\kappa_3 = (0,-\\varepsilon,0,\\varepsilon)$
    have $\\cos^2\\theta = 1/4$, i.e. they meet at $60^\\circ$: far from orthogonal. Scaling $\\kappa_2$ by
    $k > 0$ changes neither $\\kappa_3$ nor any angle, so it does not help: the rounding error in
    $\\kappa_1\\cdot\\kappa_1$ is as large as the $\\varepsilon^2$-sized quantities that should cancel."
    -- Explain: …
    rw [smul_dotProduct, smul_dotProduct, dotProduct_smul, d23, d22, d33, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    field_simp
    ring

end LinearAlgebraGame

Conclusion "
$\\cos^2\\theta = 1/4$, so $\\cos\\theta = 1/2$ (the dot product is positive): the computed vectors
meet at $60^\\circ$, not $90^\\circ$, and rescaling cannot fix an angle. Rounding $1+\\varepsilon^2$
to $1$ is an error of size $\\varepsilon^2$ — exactly the size of the quantities that were
supposed to cancel. (Chapter Six returns to stable variants such as modified Gram–Schmidt.)
"

TheoremTab "Projection"
