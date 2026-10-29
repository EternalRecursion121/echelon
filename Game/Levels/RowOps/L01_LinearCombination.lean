import Game.Metadata
import Game.Ch1

World "RowOps"
Level 1
Title "Adding equations"

Introduction "
A linear system lives in Lean as *hypotheses*: here `h1 : x + y = 5` and `h2 : x - y = 1`.
Gauss's method only ever does one thing to equations: add a multiple of one to another.

`linear_combination e` proves the goal when it is exactly the combination `e` of
hypotheses, e.g. `linear_combination h2 - h1` or `linear_combination h2 - 3 * h1`.

In this world `linarith` stays locked: you choose every combination yourself.
"

namespace LinearAlgebraGame

/-- If $x + y = 5$ and $x - y = 1$ then $2x = 6$. -/
Statement (x y : ℝ) (h1 : x + y = 5) (h2 : x - y = 1) : 2 * x = 6 := by
  Hint "Which combination of the two equations has $2x$ on the left and $6$ on the right?"
  Hint (hidden := true) "`linear_combination h1 + h2`"
  linear_combination h1 + h2

end LinearAlgebraGame

Conclusion "Lean checked that goal − (h1 + h2) is an algebraic identity."

DisabledTactic norm_num linarith nlinarith
NewTactic linear_combination
