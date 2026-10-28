import Game.Metadata
import Game.Ch3b

World "Projection"
Level 1
Title "Projection onto a line"

Introduction "
Hefferon Definition Three.VI.1.1: the orthogonal projection of $\\vec v$ into the line spanned
by a nonzero $\\vec s$ is
$$\\mathrm{proj}_{[\\vec s\\,]}(\\vec v) = \\frac{\\vec v\\cdot\\vec s}{\\vec s\\cdot\\vec s}\\,\\vec s,$$
`projLine s v` in Lean. The defining property: what is left over, $\\vec v - \\mathrm{proj}$, is
orthogonal to $\\vec s$.
"

namespace LinearAlgebraGame

open Matrix in
/-- $(\vec v - \mathrm{proj}_{[\vec s]}(\vec v))\cdot\vec s = 0$ for $\vec s \ne \vec 0$. -/
Statement projLine_orth {n : ℕ} (s v : Fin n → ℝ) (hs : s ≠ 0) :
    (v - projLine s v) ⬝ᵥ s = 0 := by
  Hint "Expand: $(\\vec v - c\\vec s)\\cdot\\vec s = \\vec v\\cdot\\vec s - c\\,(\\vec s\\cdot\\vec s)$ with
  $c = \\vec v\\cdot\\vec s / \\vec s\\cdot\\vec s$. You need $\\vec s\\cdot\\vec s \\neq 0$."
  have hss : s ⬝ᵥ s ≠ 0 := by
    Hint (hidden := true) "`intro h`, then `dotProduct_self_eq_zero.mp h` contradicts `{hs}`."
    intro h
    exact hs (dotProduct_self_eq_zero.mp h)
  Hint (hidden := true) "`rw [projLine, sub_dotProduct, smul_dotProduct, smul_eq_mul,
  div_mul_cancel₀ _ {hss}, sub_self]`"
  rw [projLine, sub_dotProduct, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hss, sub_self]

end LinearAlgebraGame

Conclusion "
So $\\vec v = \\mathrm{proj}_{[\\vec s\\,]}(\\vec v) + (\\vec v - \\mathrm{proj}_{[\\vec s\\,]}(\\vec v))$
splits $\\vec v$ into a part along $\\vec s$ and a part orthogonal to it.
"

NewDefinition LinearAlgebraGame.projLine
NewTheorem div_mul_cancel₀
TheoremTab "Projection"
