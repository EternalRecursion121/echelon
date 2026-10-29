import Game.Levels.RowOps.L01_LinearCombination

World "RowOps"
Level 2
Title "A row operation"

Introduction "
Hefferon writes $-3\\rho_1 + \\rho_2$ for \"replace row 2 by row 2 minus three times row 1\".
In this game that is the tactic

`rowop h2 := h2 - 3 * h1`

You choose the operation; Lean works out the new row and it *replaces* `h2`. For example,
with `h1 : x + y = 4` and `h2 : 3 * x + 2 * y = 10`, that step leaves `h2 : -y = -2`.
Scaling a row is `rowop h2 := -h2` (or `h2 / 3`, …).

(If you want to check your own arithmetic, write the row too:
`rowop h2 : -y = -2 := h2 - 3 * h1` — Lean then checks it instead of computing it.)

Now solve this level's system: eliminate, then back-substitute.
"

namespace LinearAlgebraGame

/-- If $x + y = 5$ and $2x + 3y = 13$ then $x = 2$ and $y = 3$. -/
Statement (x y : ℝ) (h1 : x + y = 5) (h2 : 2 * x + 3 * y = 13) : x = 2 ∧ y = 3 := by
  Hint "Eliminate $x$ from the second row: which multiple of row 1 do you subtract?"
  Hint (hidden := true) "`rowop h2 := h2 - 2 * h1`"
  rowop h2 := h2 - 2 * h1
  Hint "Now back-substitute: use the new row 2 to remove $y$ from row 1."
  Hint (hidden := true) "`rowop h1 := h1 - h2`"
  rowop h1 := h1 - h2
  Hint "Both rows are solved. Hand them to Lean as a pair."
  Hint (hidden := true) "`exact ⟨h1, h2⟩`"
  exact ⟨h1, h2⟩

end LinearAlgebraGame

Conclusion "That is Gauss's method: forward elimination, then back-substitution."

NewTactic rowop
DisabledTactic norm_num linarith nlinarith
