import Game.Levels.DotProduct.L04_SheetOneQ8

World "DotProduct"
Level 5
Title "The diagonal of a cube"

-- @sheet 1 Q6
/-! @answer
The diagonal of the unit cube in $\mathbb R^n$ is $\vec d = (1,\dots,1)$ and an axis is
$\vec e_1 = (1, 0, \dots, 0)$. Then $\vec d\cdot\vec e_1 = 1$, $|\vec d| = \sqrt n$,
$|\vec e_1| = 1$, so
$$\cos\theta = \frac{\vec d\cdot\vec e_1}{|\vec d|\,|\vec e_1|} = \frac{1}{\sqrt n},\qquad
\theta = \arccos\frac1{\sqrt n}.$$
(a) $n = 2$: $\theta = \arccos(1/\sqrt2) = \pi/4$. (b) $n = 3$: $\theta = \arccos(1/\sqrt3)
\approx 54.7^\circ$. (c) In general $\theta = \arccos(1/\sqrt n)$, which tends to $\pi/2$ as
$n \to \infty$.
-/
Introduction "
**Problem Sheet 1, Question 6.** Find the angle between the diagonal of the unit square in
$\\mathbb R^2$ (a), of the unit cube in $\\mathbb R^3$ (b), and of the unit cube in
$\\mathbb R^n$ (c), and any one of the axes.

The angle is given by $\\cos\\theta = \\dfrac{\\vec u\\cdot\\vec v}{|\\vec u|\\,|\\vec v|}$. Lean proves
the cosine for every $n \\ge 1$ (part (c)); (a) and (b) are $n = 2, 3$, and the angle is
$\\arccos$ of the result. Here the diagonal is `fun _ => 1` (all entries $1$) and the first
axis is `Pi.single ⟨0, hn⟩ 1` (entry $1$ in position $0$, zeros elsewhere).
"

namespace LinearAlgebraGame

/-- The cosine of the angle between $(1,\dots,1)$ and $\vec e_1$ in $\mathbb R^n$ is $1/\sqrt n$. -/
Statement (n : ℕ) (hn : 0 < n) :
    ((fun _ => 1 : Fin n → ℝ) ⬝ᵥ Pi.single ⟨0, hn⟩ 1) /
      (len (fun _ => 1 : Fin n → ℝ) * len (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ)) =
    1 / Real.sqrt n := by
  Hint "Compute the three ingredients: $\\vec d \\cdot \\vec d$, $\\vec e_1\\cdot\\vec e_1$ and
  $\\vec d\\cdot\\vec e_1$."
  Hint (hidden := true) "`have h₁ : (fun _ => 1 : Fin n → ℝ) ⬝ᵥ (fun _ => 1) = n := by norm_num [dotProduct]`"
  have h₁ : (fun _ => 1 : Fin n → ℝ) ⬝ᵥ (fun _ => 1) = n := by
    norm_num [dotProduct]
  Hint (strict := true) (hidden := true) "`dotProduct_single v x i : v ⬝ᵥ Pi.single i x = v i * x`.
  `have h₂ : (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) ⬝ᵥ Pi.single ⟨0, hn⟩ 1 = 1 := by`
  `rw [dotProduct_single, Pi.single_eq_same, mul_one]`"
  have h₂ : (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) ⬝ᵥ Pi.single ⟨0, hn⟩ 1 = 1 := by
    rw [dotProduct_single, Pi.single_eq_same, mul_one]
  Hint (strict := true) (hidden := true) "`rw [len, len, h₁, h₂, dotProduct_single, mul_one, Real.sqrt_one, mul_one]`"
  rw [len, len, h₁, h₂, dotProduct_single, mul_one, Real.sqrt_one, mul_one]

end LinearAlgebraGame

Conclusion "
$\\cos\\theta = 1/\\sqrt n$: (a) $\\theta = \\pi/4$; (b) $\\theta = \\arccos(1/\\sqrt 3) \\approx 54.7^\\circ$;
(c) $\\theta = \\arccos(1/\\sqrt n) \\to \\pi/2$ — in high dimension the diagonal is almost
perpendicular to every axis.
"
NewTheorem dotProduct_single Pi.single_eq_same Real.sqrt_one mul_one
