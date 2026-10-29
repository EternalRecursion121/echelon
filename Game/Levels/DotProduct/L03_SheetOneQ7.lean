import Game.Levels.DotProduct.L02_SheetTwoQ7

World "DotProduct"
Level 3
Title "Cancelling a dot product?"

-- @sheet 1 Q7
/-! @answer
**No.** Take $\vec u = (1, 0)$, $\vec v = (0, 1)$, $\vec w = (0, 2)$. Then
$\vec u\cdot\vec v = 0 = \vec u\cdot\vec w$ and $\vec u \ne \vec 0$, but $\vec v \ne \vec w$.
(All that follows is $\vec u\cdot(\vec v - \vec w) = 0$: $\vec v - \vec w \perp \vec u$.)
-/
Introduction "
**Problem Sheet 1, Question 7.** Suppose that $\\vec u \\cdot \\vec v = \\vec u \\cdot \\vec w$ and
$\\vec u \\ne \\vec 0$. Must $\\vec v = \\vec w$?

Decide: `left` (no) or `right` (yes), then prove it.
"

namespace LinearAlgebraGame

/-- Must $\vec u\cdot\vec v = \vec u\cdot\vec w$ with $\vec u \ne \vec 0$ force $\vec v = \vec w$? -/
Statement : (¬ ∀ (n : ℕ) (u v w : Fin n → ℝ), u ≠ 0 → u ⬝ᵥ v = u ⬝ᵥ w → v = w) ∨
    (∀ (n : ℕ) (u v w : Fin n → ℝ), u ≠ 0 → u ⬝ᵥ v = u ⬝ᵥ w → v = w) := by
  Hint "Decide first: what does $\\vec u\\cdot\\vec v = \\vec u\\cdot\\vec w$ say about $\\vec v - \\vec w$?"
  Hint (hidden := true) "In $\\mathbb R^2$, two different vectors can both be perpendicular to $\\vec u$."
  left
  intro h
  Hint (hidden := true) "`have hu : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by` … (look at component 0)."
  have hu : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    have h00 := congrFun h0 0
    Hint (hidden := true) "`{h00}` says entry 0 of `![1, 0]` equals entry 0 of the zero vector
    (shown `0 0`; `Pi.zero_apply` rewrites it to `0`). `norm_num at {h00}` evaluates both sides."
    norm_num at h00
  Hint (hidden := true) "`have hvw := h 2 ![1, 0] ![0, 1] ![0, 2] hu (by norm_num [dotProduct])`"
  have hvw := h 2 ![1, 0] ![0, 1] ![0, 2] hu (by norm_num [dotProduct])
  have h1 := congrFun hvw 1
  norm_num at h1

end LinearAlgebraGame

Conclusion "**Answer: no.** $\\vec u = (1,0)$, $\\vec v = (0,1)$, $\\vec w = (0,2)$."
NewTheorem dotProduct_smul smul_dotProduct add_dotProduct dotProduct_add Pi.zero_apply
