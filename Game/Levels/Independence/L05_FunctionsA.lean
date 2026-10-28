import Game.Levels.Independence.L04_PolysB

World "Independence"
Level 5
Title "x and 1/x"

-- @sheet 3 Q5a
/-! @answer
**Independent.** Suppose $a\cdot x + b\cdot\frac1x = 0$ for all $x > 0$. At $x = 1$:
$a + b = 0$. At $x = 2$: $2a + \frac b2 = 0$. From the first $b = -a$, so
$2a - \frac a2 = \frac{3a}2 = 0$, giving $a = 0$ and then $b = 0$.
-/
Introduction "
**Problem Sheet 3, Question 5.** Consider the vector space of all functions from
$\\mathbb{R}^+$ to $\\mathbb{R}$.

**(a)** Is $\\{f, g\\}$ linearly independent, where $f(x) = x$ and $g(x) = 1/x$?

In Lean $\\mathbb{R}^+$ is `PosReal`; a point is `⟨x, hx⟩` with `hx : 0 < x`, and for
`p : PosReal` the real number is `p.1`. A relation between functions holds at every point,
so you may evaluate it: `congrFun h ⟨1, one_pos⟩`.

Decide: `left` for dependent, `right` for independent.
"

namespace LinearAlgebraGame

/-- Are $x$ and $1/x$ linearly independent functions on $\mathbb{R}^+$? -/
Statement : (¬ LinearIndependent ℝ ![(fun x : PosReal => x.1), (fun x : PosReal => 1 / x.1)]) ∨
    LinearIndependent ℝ ![(fun x : PosReal => x.1), (fun x : PosReal => 1 / x.1)] := by
  Hint "If $ax + b/x = 0$ for every $x > 0$, try two convenient values of $x$."
  right
  rw [LinearIndependent.pair_iff]
  intro a b h
  Hint (hidden := true) "`have h1 := congrFun {h} ⟨1, one_pos⟩` and
  `have h2 := congrFun {h} ⟨2, two_pos⟩`, then `simp at h1 h2`."
  have h1 := congrFun h ⟨1, one_pos⟩
  have h2 := congrFun h ⟨2, two_pos⟩
  simp at h1 h2
  constructor
  · linarith
  · linarith

end LinearAlgebraGame

Conclusion "**Answer: independent.**"

NewDefinition LinearAlgebraGame.PosReal
NewTheorem one_pos two_pos
TheoremTab "Independence"
