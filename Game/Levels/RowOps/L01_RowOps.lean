import Game.Metadata
import Game.Ch1

World "RowOps"
Level 1
Title "Row operations"

Introduction "
A linear system lives in Lean as *hypotheses*: here `h1 : x + y = 5` and
`h2 : 2 * x + 3 * y = 13`. Gauss's method only ever does one thing to equations: add a
multiple of one to another.

**`rowop`.** Hefferon writes $-2\\rho_1 + \\rho_2$ for \"replace row 2 by row 2 minus twice
row 1\". In this game that is the tactic `rowop h2 := h2 - 2 * h1`: you choose the operation,
Lean works out the new row and it *replaces* `h2`. Scaling a row is `rowop h2 := -h2` (or
`h2 / 3`, …). If you want to check your own arithmetic, write the row too:
`rowop h2 : y = 3 := h2 - 2 * h1` — Lean then checks it instead of computing it.

**`linear_combination`.** When the *goal* is itself an equation, `linear_combination e`
proves it if it is exactly the combination `e` of hypotheses, e.g.
`linear_combination h1 - h2` or `linear_combination h2 - 3 * h1`.

In this world `linarith` stays locked: you choose every combination yourself.
"

namespace LinearAlgebraGame

/-- If $x + y = 5$ and $2x + 3y = 13$ then $x = 2$ and $y = 3$. -/
Statement (x y : ℝ) (h1 : x + y = 5) (h2 : 2 * x + 3 * y = 13) : x = 2 ∧ y = 3 := by
  Hint "Eliminate $x$ from the second row: which multiple of row 1 do you subtract?"
  Hint (hidden := true) "`rowop h2 := h2 - 2 * h1`"
  rowop h2 := h2 - 2 * h1
  Hint "Row 2 is solved. Split the goal into its two equations (`constructor`)."
  constructor
  · Hint "Back-substitute: which combination of `h1` and `h2` is exactly $x = 2$?"
    Hint (hidden := true) "`linear_combination h1 - h2`"
    linear_combination h1 - h2
  · Hint (hidden := true) "`exact h2`"
    exact h2

end LinearAlgebraGame

Conclusion "That is Gauss's method: forward elimination, then back-substitution. Lean
checked that goal − (h1 − h2) is an algebraic identity."

DisabledTactic norm_num linarith nlinarith
NewTactic linear_combination rowop
