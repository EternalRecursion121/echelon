import Game.Levels.RowOps.L01_LinearCombination

World "RowOps"
Level 2
Title "A row operation"

Introduction "
Hefferon writes $-2\\rho_1 + \\rho_2$ for \"replace row 2 by row 2 minus twice row 1\".
In this game that is

`rowop h₂ : y = 3 := h₂ - 2 * h₁`

You write the new row (the arithmetic is your job); Lean checks it follows from
`h₂ - 2 * h₁`, and the new row *replaces* `h₂`. Afterwards back-substitute.
"

namespace LinearAlgebraGame

/-- If $x + y = 5$ and $2x + 3y = 13$ then $x = 2$ and $y = 3$. -/
Statement (x y : ℝ) (h₁ : x + y = 5) (h₂ : 2 * x + 3 * y = 13) : x = 2 ∧ y = 3 := by
  Hint "Eliminate $x$ from the second row, then back-substitute into the first."
  Hint (hidden := true) "`rowop h₂ : y = 3 := h₂ - 2 * h₁`"
  rowop h₂ : y = 3 := h₂ - 2 * h₁
  Hint (strict := true) (hidden := true) "Now `rowop h₁ : x = 2 := h₁ - h₂`."
  rowop h₁ : x = 2 := h₁ - h₂
  Hint (strict := true) (hidden := true) "`exact ⟨h₁, h₂⟩`"
  exact ⟨h₁, h₂⟩

end LinearAlgebraGame

Conclusion "That is Gauss's method: forward elimination, then back-substitution."

NewTactic rowop
DisabledTactic norm_num linarith nlinarith
