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

The angle is given by $\\cos\\theta = \\dfrac{\\vec u\\cdot\\vec v}{|\\vec u|\\,|\\vec v|}$. Lean
works in $\\mathbb R^n$ for every $n$ (part (c)); (a) and (b) are $n = 2, 3$, and the angle is
$\\arccos$ of the cosine. The diagonal is `ones n` $= (1, \\dots, 1)$ and an axis is
`axis i` $= \\vec e_i$ (entry $1$ in position $i$, zeros elsewhere) — see the Definitions tab.
To unfold `ones` inside a dot product use `norm_num [ones, dotProduct]`: `rw [ones]` only
works on an entry `ones n i`.

The claim offers three candidate values for the cosine. Commit to one with `left` / `right`
(`right` then `left` picks the middle one), then prove it.
"

namespace LinearAlgebraGame

/-- The cosine of the angle between the diagonal $(1,\dots,1)$ and the axis $\vec e_i$ in
$\mathbb R^n$ is one of $1/n$, $1/\sqrt n$, $1/2$. -/
Statement (n : ℕ) (i : Fin n) :
    ones n ⬝ᵥ axis i / (len (ones n) * len (axis i)) = 1 / n ∨
    ones n ⬝ᵥ axis i / (len (ones n) * len (axis i)) = 1 / Real.sqrt n ∨
    ones n ⬝ᵥ axis i / (len (ones n) * len (axis i)) = 1 / 2 := by
  Hint "Compute the three ingredients on paper: $\\vec d \\cdot \\vec d$, $\\vec e_i\\cdot\\vec e_i$
  and $\\vec d\\cdot\\vec e_i$. Which option is the cosine? Then commit."
  Hint (hidden := true) "It is the middle one: `right`, then `left`."
  right
  left
  Hint "Record the three dot products as facts with `have`, then unfold `len` and rewrite."
  Hint (hidden := true) "`have h1 : ones n ⬝ᵥ ones n = n := by norm_num [ones, dotProduct]`"
  have h1 : ones n ⬝ᵥ ones n = n := by
    norm_num [ones, dotProduct]
  Hint (strict := true) (hidden := true) "`dotProduct_single v x i : v ⬝ᵥ Pi.single i x = v i * x`.
  `have h2 : axis i ⬝ᵥ axis i = 1 := by`
  `rw [axis, dotProduct_single, Pi.single_eq_same, mul_one]`"
  have h2 : axis i ⬝ᵥ axis i = 1 := by
    rw [axis, dotProduct_single, Pi.single_eq_same, mul_one]
  Hint (strict := true) (hidden := true) "`have h3 : ones n ⬝ᵥ axis i = 1 := by`
  `rw [axis, dotProduct_single, ones, mul_one]`"
  have h3 : ones n ⬝ᵥ axis i = 1 := by
    rw [axis, dotProduct_single, ones, mul_one]
  Hint (strict := true) (hidden := true) "`rw [len, len, h1, h2, h3, Real.sqrt_one, mul_one]`"
  rw [len, len, h1, h2, h3, Real.sqrt_one, mul_one]

end LinearAlgebraGame

Conclusion "
$\\cos\\theta = 1/\\sqrt n$: (a) $\\theta = \\pi/4$; (b) $\\theta = \\arccos(1/\\sqrt 3) \\approx 54.7^\\circ$;
(c) $\\theta = \\arccos(1/\\sqrt n) \\to \\pi/2$ — in high dimension the diagonal is almost
perpendicular to every axis.
"
NewTheorem dotProduct_single Pi.single_eq_same Real.sqrt_one mul_one
NewDefinition LinearAlgebraGame.ones LinearAlgebraGame.axis
